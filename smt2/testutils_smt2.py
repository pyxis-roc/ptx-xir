#!/usr/bin/env python3

import smt2ast
import subprocess
import os
import tempfile

def get_output(script, get_value_cmds, cmd, output_type):
    script = script + "\n(check-sat)\n"
    script = script + "\n".join([str(s) for s in get_value_cmds])

    h, f = tempfile.mkstemp(suffix=".smt2")
    os.close(h)

    with open(f, "w") as inp:
        inp.write(script)

    output = subprocess.check_output([cmd, f]).decode('utf-8')

    os.unlink(f)

    # note sat is a symbol and should be parseable...
    output = output.split("\n", 1)

    if output[0] == "sat":
        values = smt2ast.SMT2Parser.parse(output[1])
        out = []
        for l in values: # lines of values
            for v in l.v:
                #v.v[0]  this is the term
                value = v.v[1]
                out.append(smt2ast.from_smt2_literal(value, output_type))
        return out
    elif output[0] == "unsat":
        raise ValueError(f"SMT2 solver returned unsat: " + output[1])
    else:
        raise ValueError(f"SMT2 solver did not return sat/unsat: " + "\n".join(output))
