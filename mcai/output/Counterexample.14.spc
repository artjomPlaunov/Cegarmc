CONTROL AUTOMATON ErrorPath14

INITIAL STATE ARG0;

STATE USEFIRST ARG0 :
    MATCH "" -> GOTO ARG15;
    TRUE -> STOP;

STATE USEFIRST ARG15 :
    MATCH "extern void abort(void);" -> GOTO ARG16_1_1;
STATE USEFIRST ARG16_0_1 :
    MATCH "extern void abort(void);" -> GOTO ARG16_1_1;
STATE USEFIRST ARG16_1_1 :
    MATCH "void __VERIFIER_assert(int cond)" -> GOTO ARG16_2_1;
STATE USEFIRST ARG16_2_1 :
    MATCH "extern int __VERIFIER_nondet_int(void);" -> GOTO ARG16_3_1;
STATE USEFIRST ARG16_3_1 :
    MATCH "extern void __VERIFIER_assume(int);" -> GOTO ARG16_4_1;
STATE USEFIRST ARG16_4_1 :
    MATCH "extern void __VERIFIER_assert(int);" -> GOTO ARG16_5_1;
STATE USEFIRST ARG16_5_1 :
    MATCH "int main ()" -> GOTO ARG16_6_1;
STATE USEFIRST ARG16_6_1 :
    MATCH "" -> GOTO ARG16_7_1;
STATE USEFIRST ARG16_7_1 :
    MATCH "int x = 0;" -> GOTO ARG16_8_1;
STATE USEFIRST ARG16_8_1 :
    MATCH "int n = __VERIFIER_nondet_int();" -> GOTO ARG16_9_1;
STATE USEFIRST ARG16_9_1 :
    MATCH "int n = __VERIFIER_nondet_int();" -> GOTO ARG16_10_1;
STATE USEFIRST ARG16_10_1 :
    MATCH "int y = n;" -> GOTO ARG16_11_1;
STATE USEFIRST ARG16_11_1 :
    MATCH "int runtime_div;" -> GOTO ARG16;
    TRUE -> STOP;

STATE USEFIRST ARG16 :
    MATCH "" -> GOTO ARG1086;
    TRUE -> STOP;

STATE USEFIRST ARG1086 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1087;
    TRUE -> STOP;

STATE USEFIRST ARG1087 :
    MATCH "x++;" -> GOTO ARG1090_1_2;
STATE USEFIRST ARG1090_0_2 :
    MATCH "x++;" -> GOTO ARG1090_1_2;
STATE USEFIRST ARG1090_1_2 :
    MATCH "x++;" -> GOTO ARG1090_2_2;
STATE USEFIRST ARG1090_2_2 :
    MATCH "x++;" -> GOTO ARG1090_3_2;
STATE USEFIRST ARG1090_3_2 :
    MATCH "y--;" -> GOTO ARG1090_4_2;
STATE USEFIRST ARG1090_4_2 :
    MATCH "y--;" -> GOTO ARG1090_5_2;
STATE USEFIRST ARG1090_5_2 :
    MATCH "y--;" -> GOTO ARG1090;
    TRUE -> STOP;

STATE USEFIRST ARG1090 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1091;
    TRUE -> STOP;

STATE USEFIRST ARG1091 :
    MATCH "" -> GOTO ARG1092;
    TRUE -> STOP;

STATE USEFIRST ARG1092 :
    MATCH "[!(!(cond))]" -> GOTO ARG1094;
    TRUE -> STOP;

STATE USEFIRST ARG1094 :
    MATCH "" -> GOTO ARG1096;
    TRUE -> STOP;

STATE USEFIRST ARG1096 :
    MATCH "" -> GOTO ARG1097;
    TRUE -> STOP;

STATE USEFIRST ARG1097 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1098;
    TRUE -> STOP;

STATE USEFIRST ARG1098 :
    MATCH "" -> GOTO ARG1100;
    TRUE -> STOP;

STATE USEFIRST ARG1100 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1101;
    TRUE -> STOP;

STATE USEFIRST ARG1101 :
    MATCH "x++;" -> GOTO ARG1104_1_3;
STATE USEFIRST ARG1104_0_3 :
    MATCH "x++;" -> GOTO ARG1104_1_3;
STATE USEFIRST ARG1104_1_3 :
    MATCH "x++;" -> GOTO ARG1104_2_3;
STATE USEFIRST ARG1104_2_3 :
    MATCH "x++;" -> GOTO ARG1104_3_3;
STATE USEFIRST ARG1104_3_3 :
    MATCH "y--;" -> GOTO ARG1104_4_3;
STATE USEFIRST ARG1104_4_3 :
    MATCH "y--;" -> GOTO ARG1104_5_3;
STATE USEFIRST ARG1104_5_3 :
    MATCH "y--;" -> GOTO ARG1104;
    TRUE -> STOP;

STATE USEFIRST ARG1104 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1105;
    TRUE -> STOP;

STATE USEFIRST ARG1105 :
    MATCH "" -> GOTO ARG1106;
    TRUE -> STOP;

STATE USEFIRST ARG1106 :
    MATCH "[!(!(cond))]" -> GOTO ARG1108;
    TRUE -> STOP;

STATE USEFIRST ARG1108 :
    MATCH "" -> GOTO ARG1110;
    TRUE -> STOP;

STATE USEFIRST ARG1110 :
    MATCH "" -> GOTO ARG1111;
    TRUE -> STOP;

STATE USEFIRST ARG1111 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1112;
    TRUE -> STOP;

STATE USEFIRST ARG1112 :
    MATCH "" -> GOTO ARG1114;
    TRUE -> STOP;

STATE USEFIRST ARG1114 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1115;
    TRUE -> STOP;

STATE USEFIRST ARG1115 :
    MATCH "x++;" -> GOTO ARG1118_1_4;
STATE USEFIRST ARG1118_0_4 :
    MATCH "x++;" -> GOTO ARG1118_1_4;
STATE USEFIRST ARG1118_1_4 :
    MATCH "x++;" -> GOTO ARG1118_2_4;
STATE USEFIRST ARG1118_2_4 :
    MATCH "x++;" -> GOTO ARG1118_3_4;
STATE USEFIRST ARG1118_3_4 :
    MATCH "y--;" -> GOTO ARG1118_4_4;
STATE USEFIRST ARG1118_4_4 :
    MATCH "y--;" -> GOTO ARG1118_5_4;
STATE USEFIRST ARG1118_5_4 :
    MATCH "y--;" -> GOTO ARG1118;
    TRUE -> STOP;

STATE USEFIRST ARG1118 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1119;
    TRUE -> STOP;

STATE USEFIRST ARG1119 :
    MATCH "" -> GOTO ARG1120;
    TRUE -> STOP;

STATE USEFIRST ARG1120 :
    MATCH "[!(!(cond))]" -> GOTO ARG1122;
    TRUE -> STOP;

STATE USEFIRST ARG1122 :
    MATCH "" -> GOTO ARG1124;
    TRUE -> STOP;

STATE USEFIRST ARG1124 :
    MATCH "" -> GOTO ARG1125;
    TRUE -> STOP;

STATE USEFIRST ARG1125 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1126;
    TRUE -> STOP;

STATE USEFIRST ARG1126 :
    MATCH "" -> GOTO ARG1128;
    TRUE -> STOP;

STATE USEFIRST ARG1128 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1129;
    TRUE -> STOP;

STATE USEFIRST ARG1129 :
    MATCH "x++;" -> GOTO ARG1132_1_5;
STATE USEFIRST ARG1132_0_5 :
    MATCH "x++;" -> GOTO ARG1132_1_5;
STATE USEFIRST ARG1132_1_5 :
    MATCH "x++;" -> GOTO ARG1132_2_5;
STATE USEFIRST ARG1132_2_5 :
    MATCH "x++;" -> GOTO ARG1132_3_5;
STATE USEFIRST ARG1132_3_5 :
    MATCH "y--;" -> GOTO ARG1132_4_5;
STATE USEFIRST ARG1132_4_5 :
    MATCH "y--;" -> GOTO ARG1132_5_5;
STATE USEFIRST ARG1132_5_5 :
    MATCH "y--;" -> GOTO ARG1132;
    TRUE -> STOP;

STATE USEFIRST ARG1132 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1133;
    TRUE -> STOP;

STATE USEFIRST ARG1133 :
    MATCH "" -> GOTO ARG1134;
    TRUE -> STOP;

STATE USEFIRST ARG1134 :
    MATCH "[!(!(cond))]" -> GOTO ARG1136;
    TRUE -> STOP;

STATE USEFIRST ARG1136 :
    MATCH "" -> GOTO ARG1138;
    TRUE -> STOP;

STATE USEFIRST ARG1138 :
    MATCH "" -> GOTO ARG1139;
    TRUE -> STOP;

STATE USEFIRST ARG1139 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1140;
    TRUE -> STOP;

STATE USEFIRST ARG1140 :
    MATCH "" -> GOTO ARG1142;
    TRUE -> STOP;

STATE USEFIRST ARG1142 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1143;
    TRUE -> STOP;

STATE USEFIRST ARG1143 :
    MATCH "x++;" -> GOTO ARG1146_1_6;
STATE USEFIRST ARG1146_0_6 :
    MATCH "x++;" -> GOTO ARG1146_1_6;
STATE USEFIRST ARG1146_1_6 :
    MATCH "x++;" -> GOTO ARG1146_2_6;
STATE USEFIRST ARG1146_2_6 :
    MATCH "x++;" -> GOTO ARG1146_3_6;
STATE USEFIRST ARG1146_3_6 :
    MATCH "y--;" -> GOTO ARG1146_4_6;
STATE USEFIRST ARG1146_4_6 :
    MATCH "y--;" -> GOTO ARG1146_5_6;
STATE USEFIRST ARG1146_5_6 :
    MATCH "y--;" -> GOTO ARG1146;
    TRUE -> STOP;

STATE USEFIRST ARG1146 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1147;
    TRUE -> STOP;

STATE USEFIRST ARG1147 :
    MATCH "" -> GOTO ARG1148;
    TRUE -> STOP;

STATE USEFIRST ARG1148 :
    MATCH "[!(!(cond))]" -> GOTO ARG1150;
    TRUE -> STOP;

STATE USEFIRST ARG1150 :
    MATCH "" -> GOTO ARG1152;
    TRUE -> STOP;

STATE USEFIRST ARG1152 :
    MATCH "" -> GOTO ARG1153;
    TRUE -> STOP;

STATE USEFIRST ARG1153 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1154;
    TRUE -> STOP;

STATE USEFIRST ARG1154 :
    MATCH "" -> GOTO ARG1156;
    TRUE -> STOP;

STATE USEFIRST ARG1156 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1157;
    TRUE -> STOP;

STATE USEFIRST ARG1157 :
    MATCH "x++;" -> GOTO ARG1160_1_7;
STATE USEFIRST ARG1160_0_7 :
    MATCH "x++;" -> GOTO ARG1160_1_7;
STATE USEFIRST ARG1160_1_7 :
    MATCH "x++;" -> GOTO ARG1160_2_7;
STATE USEFIRST ARG1160_2_7 :
    MATCH "x++;" -> GOTO ARG1160_3_7;
STATE USEFIRST ARG1160_3_7 :
    MATCH "y--;" -> GOTO ARG1160_4_7;
STATE USEFIRST ARG1160_4_7 :
    MATCH "y--;" -> GOTO ARG1160_5_7;
STATE USEFIRST ARG1160_5_7 :
    MATCH "y--;" -> GOTO ARG1160;
    TRUE -> STOP;

STATE USEFIRST ARG1160 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1161;
    TRUE -> STOP;

STATE USEFIRST ARG1161 :
    MATCH "" -> GOTO ARG1162;
    TRUE -> STOP;

STATE USEFIRST ARG1162 :
    MATCH "[!(!(cond))]" -> GOTO ARG1164;
    TRUE -> STOP;

STATE USEFIRST ARG1164 :
    MATCH "" -> GOTO ARG1166;
    TRUE -> STOP;

STATE USEFIRST ARG1166 :
    MATCH "" -> GOTO ARG1167;
    TRUE -> STOP;

STATE USEFIRST ARG1167 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1168;
    TRUE -> STOP;

STATE USEFIRST ARG1168 :
    MATCH "" -> GOTO ARG1170;
    TRUE -> STOP;

STATE USEFIRST ARG1170 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1171;
    TRUE -> STOP;

STATE USEFIRST ARG1171 :
    MATCH "x++;" -> GOTO ARG1174_1_8;
STATE USEFIRST ARG1174_0_8 :
    MATCH "x++;" -> GOTO ARG1174_1_8;
STATE USEFIRST ARG1174_1_8 :
    MATCH "x++;" -> GOTO ARG1174_2_8;
STATE USEFIRST ARG1174_2_8 :
    MATCH "x++;" -> GOTO ARG1174_3_8;
STATE USEFIRST ARG1174_3_8 :
    MATCH "y--;" -> GOTO ARG1174_4_8;
STATE USEFIRST ARG1174_4_8 :
    MATCH "y--;" -> GOTO ARG1174_5_8;
STATE USEFIRST ARG1174_5_8 :
    MATCH "y--;" -> GOTO ARG1174;
    TRUE -> STOP;

STATE USEFIRST ARG1174 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1175;
    TRUE -> STOP;

STATE USEFIRST ARG1175 :
    MATCH "" -> GOTO ARG1176;
    TRUE -> STOP;

STATE USEFIRST ARG1176 :
    MATCH "[!(!(cond))]" -> GOTO ARG1178;
    TRUE -> STOP;

STATE USEFIRST ARG1178 :
    MATCH "" -> GOTO ARG1180;
    TRUE -> STOP;

STATE USEFIRST ARG1180 :
    MATCH "" -> GOTO ARG1181;
    TRUE -> STOP;

STATE USEFIRST ARG1181 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1182;
    TRUE -> STOP;

STATE USEFIRST ARG1182 :
    MATCH "" -> GOTO ARG1184;
    TRUE -> STOP;

STATE USEFIRST ARG1184 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1185;
    TRUE -> STOP;

STATE USEFIRST ARG1185 :
    MATCH "x++;" -> GOTO ARG1188_1_9;
STATE USEFIRST ARG1188_0_9 :
    MATCH "x++;" -> GOTO ARG1188_1_9;
STATE USEFIRST ARG1188_1_9 :
    MATCH "x++;" -> GOTO ARG1188_2_9;
STATE USEFIRST ARG1188_2_9 :
    MATCH "x++;" -> GOTO ARG1188_3_9;
STATE USEFIRST ARG1188_3_9 :
    MATCH "y--;" -> GOTO ARG1188_4_9;
STATE USEFIRST ARG1188_4_9 :
    MATCH "y--;" -> GOTO ARG1188_5_9;
STATE USEFIRST ARG1188_5_9 :
    MATCH "y--;" -> GOTO ARG1188;
    TRUE -> STOP;

STATE USEFIRST ARG1188 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1189;
    TRUE -> STOP;

STATE USEFIRST ARG1189 :
    MATCH "" -> GOTO ARG1190;
    TRUE -> STOP;

STATE USEFIRST ARG1190 :
    MATCH "[!(!(cond))]" -> GOTO ARG1192;
    TRUE -> STOP;

STATE USEFIRST ARG1192 :
    MATCH "" -> GOTO ARG1194;
    TRUE -> STOP;

STATE USEFIRST ARG1194 :
    MATCH "" -> GOTO ARG1195;
    TRUE -> STOP;

STATE USEFIRST ARG1195 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1196;
    TRUE -> STOP;

STATE USEFIRST ARG1196 :
    MATCH "" -> GOTO ARG1198;
    TRUE -> STOP;

STATE USEFIRST ARG1198 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1199;
    TRUE -> STOP;

STATE USEFIRST ARG1199 :
    MATCH "x++;" -> GOTO ARG1202_1_10;
STATE USEFIRST ARG1202_0_10 :
    MATCH "x++;" -> GOTO ARG1202_1_10;
STATE USEFIRST ARG1202_1_10 :
    MATCH "x++;" -> GOTO ARG1202_2_10;
STATE USEFIRST ARG1202_2_10 :
    MATCH "x++;" -> GOTO ARG1202_3_10;
STATE USEFIRST ARG1202_3_10 :
    MATCH "y--;" -> GOTO ARG1202_4_10;
STATE USEFIRST ARG1202_4_10 :
    MATCH "y--;" -> GOTO ARG1202_5_10;
STATE USEFIRST ARG1202_5_10 :
    MATCH "y--;" -> GOTO ARG1202;
    TRUE -> STOP;

STATE USEFIRST ARG1202 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1203;
    TRUE -> STOP;

STATE USEFIRST ARG1203 :
    MATCH "" -> GOTO ARG1204;
    TRUE -> STOP;

STATE USEFIRST ARG1204 :
    MATCH "[!(!(cond))]" -> GOTO ARG1206;
    TRUE -> STOP;

STATE USEFIRST ARG1206 :
    MATCH "" -> GOTO ARG1208;
    TRUE -> STOP;

STATE USEFIRST ARG1208 :
    MATCH "" -> GOTO ARG1209;
    TRUE -> STOP;

STATE USEFIRST ARG1209 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1210;
    TRUE -> STOP;

STATE USEFIRST ARG1210 :
    MATCH "" -> GOTO ARG1212;
    TRUE -> STOP;

STATE USEFIRST ARG1212 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1213;
    TRUE -> STOP;

STATE USEFIRST ARG1213 :
    MATCH "x++;" -> GOTO ARG1216_1_11;
STATE USEFIRST ARG1216_0_11 :
    MATCH "x++;" -> GOTO ARG1216_1_11;
STATE USEFIRST ARG1216_1_11 :
    MATCH "x++;" -> GOTO ARG1216_2_11;
STATE USEFIRST ARG1216_2_11 :
    MATCH "x++;" -> GOTO ARG1216_3_11;
STATE USEFIRST ARG1216_3_11 :
    MATCH "y--;" -> GOTO ARG1216_4_11;
STATE USEFIRST ARG1216_4_11 :
    MATCH "y--;" -> GOTO ARG1216_5_11;
STATE USEFIRST ARG1216_5_11 :
    MATCH "y--;" -> GOTO ARG1216;
    TRUE -> STOP;

STATE USEFIRST ARG1216 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1217;
    TRUE -> STOP;

STATE USEFIRST ARG1217 :
    MATCH "" -> GOTO ARG1218;
    TRUE -> STOP;

STATE USEFIRST ARG1218 :
    MATCH "[!(!(cond))]" -> GOTO ARG1220;
    TRUE -> STOP;

STATE USEFIRST ARG1220 :
    MATCH "" -> GOTO ARG1222;
    TRUE -> STOP;

STATE USEFIRST ARG1222 :
    MATCH "" -> GOTO ARG1223;
    TRUE -> STOP;

STATE USEFIRST ARG1223 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1224;
    TRUE -> STOP;

STATE USEFIRST ARG1224 :
    MATCH "" -> GOTO ARG1226;
    TRUE -> STOP;

STATE USEFIRST ARG1226 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1227;
    TRUE -> STOP;

STATE USEFIRST ARG1227 :
    MATCH "x++;" -> GOTO ARG1230_1_12;
STATE USEFIRST ARG1230_0_12 :
    MATCH "x++;" -> GOTO ARG1230_1_12;
STATE USEFIRST ARG1230_1_12 :
    MATCH "x++;" -> GOTO ARG1230_2_12;
STATE USEFIRST ARG1230_2_12 :
    MATCH "x++;" -> GOTO ARG1230_3_12;
STATE USEFIRST ARG1230_3_12 :
    MATCH "y--;" -> GOTO ARG1230_4_12;
STATE USEFIRST ARG1230_4_12 :
    MATCH "y--;" -> GOTO ARG1230_5_12;
STATE USEFIRST ARG1230_5_12 :
    MATCH "y--;" -> GOTO ARG1230;
    TRUE -> STOP;

STATE USEFIRST ARG1230 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1231;
    TRUE -> STOP;

STATE USEFIRST ARG1231 :
    MATCH "" -> GOTO ARG1232;
    TRUE -> STOP;

STATE USEFIRST ARG1232 :
    MATCH "[!(!(cond))]" -> GOTO ARG1234;
    TRUE -> STOP;

STATE USEFIRST ARG1234 :
    MATCH "" -> GOTO ARG1236;
    TRUE -> STOP;

STATE USEFIRST ARG1236 :
    MATCH "" -> GOTO ARG1237;
    TRUE -> STOP;

STATE USEFIRST ARG1237 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1238;
    TRUE -> STOP;

STATE USEFIRST ARG1238 :
    MATCH "" -> GOTO ARG1240;
    TRUE -> STOP;

STATE USEFIRST ARG1240 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1241;
    TRUE -> STOP;

STATE USEFIRST ARG1241 :
    MATCH "x++;" -> GOTO ARG1244_1_13;
STATE USEFIRST ARG1244_0_13 :
    MATCH "x++;" -> GOTO ARG1244_1_13;
STATE USEFIRST ARG1244_1_13 :
    MATCH "x++;" -> GOTO ARG1244_2_13;
STATE USEFIRST ARG1244_2_13 :
    MATCH "x++;" -> GOTO ARG1244_3_13;
STATE USEFIRST ARG1244_3_13 :
    MATCH "y--;" -> GOTO ARG1244_4_13;
STATE USEFIRST ARG1244_4_13 :
    MATCH "y--;" -> GOTO ARG1244_5_13;
STATE USEFIRST ARG1244_5_13 :
    MATCH "y--;" -> GOTO ARG1244;
    TRUE -> STOP;

STATE USEFIRST ARG1244 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1245;
    TRUE -> STOP;

STATE USEFIRST ARG1245 :
    MATCH "" -> GOTO ARG1246;
    TRUE -> STOP;

STATE USEFIRST ARG1246 :
    MATCH "[!(!(cond))]" -> GOTO ARG1248;
    TRUE -> STOP;

STATE USEFIRST ARG1248 :
    MATCH "" -> GOTO ARG1250;
    TRUE -> STOP;

STATE USEFIRST ARG1250 :
    MATCH "" -> GOTO ARG1251;
    TRUE -> STOP;

STATE USEFIRST ARG1251 :
    MATCH "runtime_div = x/(n-y);" -> GOTO ARG1252;
    TRUE -> STOP;

STATE USEFIRST ARG1252 :
    MATCH "" -> GOTO ARG1254;
    TRUE -> STOP;

STATE USEFIRST ARG1254 :
    MATCH "[x+y <= 999999]" -> GOTO ARG1255;
    TRUE -> STOP;

STATE USEFIRST ARG1255 :
    MATCH "x++;" -> GOTO ARG1258_1_14;
STATE USEFIRST ARG1258_0_14 :
    MATCH "x++;" -> GOTO ARG1258_1_14;
STATE USEFIRST ARG1258_1_14 :
    MATCH "x++;" -> GOTO ARG1258_2_14;
STATE USEFIRST ARG1258_2_14 :
    MATCH "x++;" -> GOTO ARG1258_3_14;
STATE USEFIRST ARG1258_3_14 :
    MATCH "y--;" -> GOTO ARG1258_4_14;
STATE USEFIRST ARG1258_4_14 :
    MATCH "y--;" -> GOTO ARG1258_5_14;
STATE USEFIRST ARG1258_5_14 :
    MATCH "y--;" -> GOTO ARG1258;
    TRUE -> STOP;

STATE USEFIRST ARG1258 :
    MATCH "__VERIFIER_assert( (n-y) > 0);" -> GOTO ARG1259;
    TRUE -> STOP;

STATE USEFIRST ARG1259 :
    MATCH "" -> GOTO ARG1260;
    TRUE -> STOP;

STATE USEFIRST ARG1260 :
    MATCH "[!(cond)]" -> GOTO ARG1261;
    TRUE -> STOP;

STATE USEFIRST ARG1261 :
    MATCH "ERROR: {abort();}" -> ERROR;
    TRUE -> STOP;

STATE USEFIRST ARG1264 :
    TRUE -> STOP;

END AUTOMATON