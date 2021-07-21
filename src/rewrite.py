#!/usr/bin/env python3
#
# rewrite.py
# Decouple handling of Pythonisms in the PTX XIR from XIR proper.
#
# Author: Sreepathi Pai

import ast
import argparse
import astunparse

ROUND_SAT_ARITH_FNS = set(['ADD_ROUND', 'SUB_ROUND', 'MUL_ROUND', 'DIV_ROUND', 'FMA_ROUND', 'SQRT_ROUND', 'RCP_ROUND',  'ADD_ROUND_SATURATE',  'SUB_ROUND_SATURATE', 'MUL_ROUND_SATURATE', 'FMA_ROUND_SATURATE'])

class RewritePythonisms(ast.NodeTransformer):
    desugar_boolean_xor = True
    elim_x_value = False

    def _is_float_constant_constructor(self, n):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == 'float':
            if isinstance(n.args[0], ast.Str):
                return n.args[0].s.lower() in ("nan",
                                               "+nan",
                                               "-nan",
                                               "+nan",
                                               "+inf",
                                               "inf",
                                               "-inf",
                                               "-0.0")
        return False

    # TODO: handle machine_specific

    # unused, delete after verification
    # def _add_rounding(self, n):
    #     if isinstance(n.func, ast.Name) and "_ROUND" in n.func.id: #TODO: make a full list?
    #         assert isinstance(n.args[-1], ast.Str), f"Expecting last argument of ROUND function to be a string"
    #         roundModifier = n.args.pop().s
    #         n.func.id = n.func.id.replace('_ROUND', '_ROUND_' + roundModifier)

    def cvt_machine_specific(self, node):
        def get_keys(msn, keys=None):
            if isinstance(msn, ast.Subscript):
                if isinstance(msn.value, ast.Name) and msn.value.id == 'machine_specific':
                    assert isinstance(msn.slice.value, ast.Str), f"Don't support {msn.slice}"
                    v = msn.slice.value.s
                    keys.append(v)
                    return True
                elif isinstance(msn.value, ast.Subscript):
                    if get_keys(msn.value, keys):
                        assert isinstance(msn.slice.value, ast.Str), f"Don't support {msn.slice}"
                        v = msn.slice.value.s
                        keys.append(v)
                        return True
                    else:
                        return False
                else:
                    return False
            else:
                return False

        k = []
        if get_keys(node, k):
            return ast.Name("MACHINE_SPECIFIC_" + "_".join(k), node.ctx)
        else:
            return node

    def visit_Subscript(self, node):
        if isinstance(node.value, ast.Subscript):
            return self.cvt_machine_specific(node)

        return self.generic_visit(node)

    SUFFIX_FNS = {'compare': (2, ast.Str),
                  'zext': (1, ast.Num),
                  'ReadByte': (0, (ast.Str, ast.NameConstant)),
                  'truncate': (1, ast.Num),
                  'sext': (1, ast.Num),
                  }

    def add_fn_suffix(self, node):
        argid, arg_type = self.SUFFIX_FNS[node.func.id]
        arg = node.args[argid]

        assert isinstance(arg, arg_type), f"{node.func.id} does not have {arg_type} as argument #{argid}, actual type is {type(arg)}"
        if isinstance(arg, ast.Str):
            suffix = arg.s
        elif isinstance(arg, ast.Num):
            suffix = str(arg.n)
        elif isinstance(arg, ast.NameConstant):
            if arg.value is None:
                suffix = ''
            else:
                raise NotImplementedError(f"Don't support NamedConstant with value = {arg.value}")
        else:
            raise NotImplementedError(f"Don't support {arg_type} as suffix")

        node.func.id = node.func.id + ('_' + suffix if suffix else '')
        del node.args[argid]
        self.generic_visit(node)
        return node

    def visit_Call(self, node):
        if isinstance(node.func, ast.Name):
            if node.func.id in self.SUFFIX_FNS:
                return self.add_fn_suffix(node)
            elif node.func.id.startswith('extractAndSignOrZeroExt'):
                assert isinstance(node.args[2], ast.Num) and node.args[2].n == 32
                assert isinstance(node.args[1], ast.NameConstant) and node.args[1].value in (True, False)
                # This is not necessary, but could simplify implementations?
                if node.args[1].value == False:
                    node.func.id = "extractAndZeroExt" + node.func.id[len("extractAndSignOrZeroExt"):]
                elif node.args[1].value == True:
                    node.func.id = "extractAndSignExt" + node.func.id[len("extractAndSignOrZeroExt"):]
                else:
                    assert False, f"Unsupported {node.args[1].value}"

                node.args = node.args[0:1] # this will happen before Assign
            elif node.func.id in ROUND_SAT_ARITH_FNS:
                if node.func.id == 'FMA_ROUND' or node.func.id == 'FMA_ROUND_SATURATE':
                    node.args.insert(3, node.args[-1])
                    node.args.pop()
                elif node.func.id in ('RCP_ROUND', 'SQRT_ROUND'):
                    node.args.insert(1, node.args[-1])
                    node.args.pop()
                else:
                    node.args.insert(2, node.args[-1])
                    node.args.pop()

            elif node.func.id == 'booleanOp':
                assert isinstance(node.args[2], ast.Str)
                if node.args[2].s == 'and':
                    node = ast.BoolOp(op=ast.And(), values=[node.args[0], node.args[1]])
                elif node.args[2].s == 'or':
                    node = ast.BoolOp(op=ast.Or(), values=[node.args[0], node.args[1]])
                elif node.args[2].s == 'xor':
                    if self.desugar_boolean_xor:
                        # ugly but this is boolean xor: a'b + ab'
                        node = ast.BoolOp(op=ast.Or(),
                                          values=[ast.BoolOp(op=ast.And(),
                                                             values=[ast.UnaryOp(ast.Not(),
                                                                                 node.args[0]),
                                                                     node.args[1]]),

                                                  ast.BoolOp(op=ast.And(),
                                                             values=[node.args[0],
                                                                     ast.UnaryOp(ast.Not(),
                                                                                 node.args[1])]),
                                          ])
                    else:
                        node.func.id = 'booleanOp_' + node.args[2].s
                        node.args.pop()

                return node
            elif node.func.id == 'EQ' or node.func.id == 'NOTEQ':
                if self._is_float_constant_constructor(node.args[1]):
                    return ast.Call(func=ast.Name(f"FLOAT_COMPARE_{node.func.id}", ast.Load()),
                                    args=[node.args[0], node.args[1]],
                                    keywords={})
            elif node.func.id == 'float':
                if not isinstance(node.args[0], ast.Str):
                    return node.args[0] # don't support float as a type cast
            elif node.func.id == 'int':
                return node.args[0] # don't support int as a type cast
            elif node.func.id == 'range':
                if len(node.args) != 2:
                    # though we should support step...
                    raise NotImplementedError(f"range with {len(node.args)} not supported")

                if not (isinstance(node.args[0], ast.Num) and isinstance(node.args[1], ast.Num)):
                    raise NotImplementedError(f"range with non-constant arguments not supported")
            elif node.func.id in ('SHL', 'SHR', 'SAR'):
                node = self.generic_visit(node)
                #TODO: the greater than is because of PTX...
                assert len(node.args) >= 2, f"{node.func.id} needs two arguments" 
                if isinstance(node.args[1], ast.Num):
                    node.func.id = node.func.id + "_LIT"
            elif node.func.id == 'BITSTRING':
                node = self.generic_visit(node)
                assert isinstance(node.args[3], ast.Num), f"BITSTRING needs a constant size: {node.args[3]}"
                node.func.id += "_" + str(node.args[3].n)
            elif node.func.id == 'FROM_BITSTRING':
                node = self.generic_visit(node)
                assert isinstance(node.args[1], ast.Num), f"FROM_BITSTRING needs a constant size: {node.args[1]}"
                node.func.id += "_" + str(node.args[1].n)
            elif self.elim_x_value and node.func.id == 'set_value':
                # ptx relies on set_value to set type on argument, once
                # type annotations are on _global_*, we can get rid of self.noptx
                # get rid of set_value, since it's not needed
                return node.args[2]
            elif self.elim_x_value and node.func.id == 'get_value':
                node = self.generic_visit(node)
                # get rid of get_value, since it's not needed
                return node.args[2]
            else:
                node = self.generic_visit(node)
        else:
            node = self.generic_visit(node)

        return node

    def visit_Assign(self, node):
        # rewrite extractAnd*Ext so that we can support languages that don't support returning arrays
        node = self.generic_visit(node)

        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if isinstance(node.value, ast.Call):
                if isinstance(node.value.func, ast.Name) and node.value.func.id.startswith('extractAnd'):
                    width = int(node.value.func.id[-1:]) # _2 or _4
                    rhs = node.value
                    rhs.args.append(node.targets[0])
                    return [ast.AnnAssign(target=ast.Name(id=node.targets[0].id),
                                          annotation=ast.Subscript(value=ast.Name(id="u32"),
                                                                   slice=ast.Num(n=width),
                                          ),
                                          value=None,
                                          simple=1),
                            ast.Expr(rhs)]

        return node

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Rewrite legacy Pythonisms in the PTX XIR")
    p.add_argument("input", help="Input file")
    p.add_argument("output", help="Output file")

    args = p.parse_args()

    with open(args.input, 'r') as f:
        inpast = ast.parse(f.read(), filename=args.input)

    rp = RewritePythonisms()
    rp.elim_x_value = True
    
    outast = rp.visit(inpast)

    with open(args.output, 'w') as f:
        f.write(astunparse.unparse(outast))
