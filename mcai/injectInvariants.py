import os
import time

inputFile = "test1-ACSL"
cmd = f"frama-c -eva -eva-domains octagon -eva-msg-key d-octagon"

file = open(inputFile + ".c", 'r')

outputFile = inputFile + "-eva.c"
f = open(outputFile, "a")
#f.writelines(["See you soon!", "Over and out."])
#f.close()


while line := file.readline() :
    if "__FRAMAC_OCTAGON:" in line:
        f.writelines(["Frama_C_dump_each();\n", line])
    else:
        f.writelines([line])

f.close()
os.system(cmd + " " + outputFile)


