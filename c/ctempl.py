#!/usr/bin/env python3

import argparse
import pycparser
from pycparser import c_ast, c_generator, c_parser
import tempfile
from collections import OrderedDict, namedtuple
import copy

CGeneric = namedtuple('CGeneric', 'name args control assoc_list')

class Instantiate(c_ast.NodeVisitor):
    def visit_IdentifierType(self, node):
        if len(node.names) == 1:
            v = node.names[0]
            if v in self._dtvast:
                #print(v, self._dtvast[v])
                node.names = self._dtvast[v].type.names

    def visit_FuncDef(self, node):
        # there is only one Funcdef

        # this doesn't change the name ...
        node.decl.name = self._funcname

        # funcdecl.decl).type.declname
        node.decl.type.type.declname = self._funcname
        self.generic_visit(node)

    def instantiate(self, dtvast, tmplast, funcname):
        self._dtvast = dtvast
        self._funcname = funcname
        self.visit(tmplast)

def load_template(cfile, headers):
    src = pycparser.parse_file(cfile, use_cpp=True, cpp_args=["-I{headers}"])
    out = {}
    template_vars = {}
    for d in src.ext: # should work in pycparse < 2.19
        if isinstance(d, c_ast.Typedef):
            if d.coord.file == cfile:
                if d.name[0] == "T": # unnecessary convention?
                    template_vars[d.name] = d
        elif isinstance(d, c_ast.FuncDef):
            n = d.decl.name
            out[n] = d

    return template_vars, out

def get_typedefs_for_tvars(varvalues):
    o = []
    for v in varvalues:
        v, vt = v.split("=")
        o.append((v, f"typedef {vt} {v};"))

    return OrderedDict(o)

def instantiate(tmplname, funcname, tvals, ctempl, tvars, headers):
    assert tmplname in ctempl, f"Unknown template function {tmplname}"

    # parse template variable instantiations
    with tempfile.NamedTemporaryFile(mode='w', suffix=".c") as f:
        f.write(headers)
        ccode = "\n".join([v for v in tvals.values()])
        f.write(ccode)
        f.flush()

        tint = pycparser.parse_file(f.name, use_cpp=True, cpp_args=["-I{headers}"])

    # extract ASTs
    out = {}
    for d in tint.ext:
        if isinstance(d, c_ast.Typedef):
            if d.name in tvars:
                out[d.name] = d.type

    tmpl = copy.deepcopy(ctempl[tmplname])

    ti = Instantiate()
    ti.instantiate(out, tmpl, funcname)

    cg = c_generator.CGenerator()
    return out, cg.visit(tmpl)

def generate_generics(generics, instantiations):
    out = []
    for g in generics:
        tmplname, args, tvar_typename, control = g
        args = ', '.join(args.split(":"))
        assert tmplname in instantiations, f"Generic {tmplname} has not been instantiated"

        assoc_list = []
        for i in instantiations[tmplname]:
            funcname, tvals = i
            # typedef XYZ ABC T0;
            tval_typename = tvals[tvar_typename][len("typedef "):-len(tvar_typename)-1] # yuck...
            assoc_list.append((tval_typename.strip(), funcname))

        yield CGeneric(name=tmplname, args=args, control = control, assoc_list = assoc_list)

def process_script(script, output, fakecheaders = '/usr/share/python-pycparser/fake_libc_include'):
    ctempl = None
    headers = []
    instantiations = {}
    generics = []

    with open(script, "r") as f:
        for l in f:
            l = l.strip()
            if not l: continue # blank line
            if l[0] == "#": continue # comment

            if l.startswith("template "):
                assert ctempl is None, f"Duplicate template lines in script"
                ctempl = ' '.join(l.split()[1:])
            elif l.startswith("tvar_include "):
                hdr = l.split(' ', 1)[1]
                headers.append(f"#include {hdr.strip()}")
            elif l.startswith("inst"):
                # inst tmplfunc funcname tvar1=tval1:tvar2=tval2
                inst = l.split()
                tvars = get_typedefs_for_tvars(inst[3].split(':'))
                if inst[1] not in instantiations:
                    instantiations[inst[1]] = []

                instantiations[inst[1]].append((inst[2], tvars))
            elif l.startswith("generic"):
                gen = l.split()
                if len(gen) > 5:
                    gen[4] = ' '.join(gen[4:]) # expression is last and can contain ' '

                generics.append((gen[1], gen[2], gen[3], gen[4]))

    tvars, ctempl = load_template(ctempl, fakecheaders)
    headers = "\n".join(headers) + "\n"

    print("#pragma once", file=output)
    print(headers, file=output)
    for tmplfunc in instantiations.keys():
        for funcname, tvals in instantiations[tmplfunc]:
            _, code = instantiate(tmplfunc, funcname, tvals, ctempl, tvars, headers)
            print(code, file=output)

    print("#if __STDC_VERSION__ >= 201101L", file=output)
    for g in generate_generics(generics, instantiations):
        d = f"#define {g.name}({g.args}) _Generic("
        print(f"{d}{g.control}, " + "\\", file=output)
        print(", \\\n".join([" "*len(d) + f"{t}: {f}" for t, f in g.assoc_list]), end='', file=output)
        print(f")({g.args})\n", file=output)
    print("#endif", file=output)

if __name__ == "__main__":
    import sys

    if sys.argv[0].endswith("ctempl_script.py"):
        p = argparse.ArgumentParser(description="Produce `generic' C code from templates")

        p.add_argument("script", help="C template file using typedefs as templates")
        p.add_argument("output", nargs="?", help="Output file")
        p.add_argument('--fakecheaders', help="Fake C headers for pycparser", default="/usr/share/python-pycparser/fake_libc_include") # this assumes that a pycparser package is installed

        args = p.parse_args()
        if args.output:
            f = open(args.output, "w")
        else:
            f = sys.stdout

        process_script(args.script, f)
    else:
        p = argparse.ArgumentParser(description="Produce `generic' C code from templates")

        p.add_argument("ctempl", help="C template file using typedefs as templates")
        p.add_argument("tmplfunc", help="Function template name")
        p.add_argument("funcname", help="Function instantiatiation name")
        p.add_argument("variables", nargs="+", help="Template variable assignments (templatevar=templatetype)")
        p.add_argument('--fakecheaders', help="Fake C headers for pycparser", default="/usr/share/python-pycparser/fake_libc_include") # this assumes that a pycparser package is installed

        args = p.parse_args()

        tvars, ctempl = load_template(args.ctempl, args.fakecheaders)
        tvals = get_typedefs_for_tvars(args.variables)
        instantiate(args.tmplfunc, args.funcname, tvals, ctempl, tvars, "#include <stdint.h>\n")

