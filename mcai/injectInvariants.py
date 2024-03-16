import os
import time

inputFile = "test1-ACSL.c"
in_file = open(inputFile, 'r')

outputFile = "test1-ACSL-eva.c"

framac_file = open(outputFile, "a")

counter = 0
while line := in_file.readline() :
    if "__FRAMAC_OCTAGON:" in line:
        framac_file.writelines(["Frama_C_dump_each();\n", line])
        counter += 1
    else:
        framac_file.writelines([line])

framac_file.close()
in_file.close()

cmd = f"frama-c -eva -eva-domains octagon -eva-msg-key d-octagon {outputFile}"
os.system(cmd)


