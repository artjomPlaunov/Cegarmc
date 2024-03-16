import os
import time

def run_eva(input_fname, octagon_fname):
    in_file = open(input_fname, 'r')
    framac_fname = "test1-ACSL-eva.c"
    framac_file = open(framac_fname, "a")
    while line := in_file.readline() :
        if "__FRAMAC_OCTAGON" in line:
            framac_file.writelines(["Frama_C_dump_each(); " + line])
        else:
            framac_file.writelines([line])
    framac_file.close()
    in_file.close()
    cmd = f"frama-c -eva -eva-domains octagon -eva-msg-key d-octagon {framac_fname} >> {octagon_fname}"
    os.system(cmd)

def get_octagon_results(octagon_fname):
    # Read octagon analysis results into list. 
    octagon_results = []
    octagon_file = open(octagon_fname, "r")
    while line := octagon_file.readline():
        octagon_results.append(line)
    octagon_file.close()
    return octagon_results

def parse_nondet_interval(interval):
    lhs, rhs = interval.split('=')
    rhs = rhs.strip()
    rhs = rhs.replace("Frama_C_interval(", "")
    rhs = rhs.replace(");", "")
    lo,hi = rhs.split(',')
    var = lhs.replace("int", "")
    if lo == "INT_MIN":
        lo = "–2147483648"
    if hi == "INT_MAX":
        hi = 2147483647
    return f"int {var} = __VERIFIER_nondet_int();\n if ({var} < {lo} || {var} > {hi}) abort();\n"

def generate_cpa_file(input_fname, cpa_fname, octagon_results):
    cpa_file = open(cpa_fname, "a")
    in_file = open(input_fname, 'r')
    cpa_header_file = open("cpa_defs.h", "r")
    while line := cpa_header_file.readline():
         cpa_file.writelines([line])
    cpa_header_file.close()   


    line_num = 1 
    while line := in_file.readline(): 
        if "__FRAMAC_OCTAGON" in line:
            invariants = read_invariants(octagon_results, line_num)
            cpa_file.writelines([line] + invariants)
        elif "Frama_C_interval" in line:
            nondet = parse_nondet_interval(line)
            cpa_file.writelines([nondet])
        elif "__fc_builtin.h" in line:
            line_num += 1
            continue
        else:
            cpa_file.writelines([line])
        line_num += 1

def read_last_invariant(octagon_results, lnum):
    for i in range(len(octagon_results)):
        if f"-eva.c:{lnum}" in octagon_results[i]:
            res = []
            if "Frama_C_dump_each" in octagon_results[i+1]:
                dump = []
                # start at Frama_C_dump_each (exclusive) 
                # go till END OF DUMP (exclusive) 
                j = i+2
                while "END OF DUMP" not in octagon_results[j]:
                    dump.append(octagon_results[j])
                    j += 1
                # start at the end of lines (not including END OF DUMP)
                # iterate till you see octagon in lines
                i = len(dump)-1
                while i > 0 and "octagon" not in dump[i]:
                    i -= 1
                res = dump[i+1:]
    return res

def cleanup(l):
    l = l.strip()
    l = l.replace(' ', '')
    l = l.replace('{[', '')
    l = l.replace(']}', '')
    return l

def parse_interval(lhs,rhs):
    # trim off the brackets
    if len(rhs) >= 2:
        rhs = rhs[1:-1]
    lo, hi = rhs.split('..')
    if lo == '--':
        lo = 'INT_MIN'
    if hi == '--':
        hi = 'INT_MAX'
    return f'{lo}<={lhs}&&{lhs}<={hi}'

def parse_set(lhs, rhs):
    if len(rhs) >= 2:
        rhs = rhs[1:-1]
    # trim off brackets
    rhs = rhs.replace(';', ',')
    numbers = rhs.split(',')
    print(numbers)
    
    return '||'.join(map(lambda num: f'{lhs}=={num}', numbers))
         

def parse_octagon(octagon):
    lhs, rhs = octagon.split('∈')
    if "{" in rhs:
        assume = parse_set(lhs, rhs)
    if "[" in rhs:
        assume =  parse_interval(lhs, rhs)
    return f"__VERIFIER_assume({assume});\n"


def read_invariants(octagon_results, lnum):
    octagon_text = read_last_invariant(octagon_results, lnum)
    octagon_text = list(map(cleanup, octagon_text))
    # filter out lines without \exists
    octagon_text = list(filter(lambda s: len(s)>0, octagon_text))
    res = []
    for octagon in octagon_text:
        res.append(parse_octagon(octagon))
    return res 
    
if __name__ == "__main__":
    input_fname = "test1-ACSL.c"
    octagon_fname = "octagon_results.txt"
    cpa_fname = "test1-ACSL-cpa.c"

    run_eva(input_fname, octagon_fname)
    octagon_results = get_octagon_results(octagon_fname)
    generate_cpa_file(input_fname, cpa_fname, octagon_results)
    for fname in [input_fname, cpa_fname]:
        os.system(f"clang-format -i {fname}")
