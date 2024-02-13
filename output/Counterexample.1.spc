CONTROL AUTOMATON ErrorPath1

INITIAL STATE ARG0;

STATE USEFIRST ARG0 :
    MATCH "" -> GOTO ARG1;
    TRUE -> STOP;

STATE USEFIRST ARG1 :
    MATCH "extern void abort(void);" -> GOTO ARG2_1_1;
STATE USEFIRST ARG2_0_1 :
    MATCH "extern void abort(void);" -> GOTO ARG2_1_1;
STATE USEFIRST ARG2_1_1 :
    MATCH "void __VERIFIER_assert(int cond)" -> GOTO ARG2_2_1;
STATE USEFIRST ARG2_2_1 :
    MATCH "extern int __VERIFIER_nondet_int(void);" -> GOTO ARG2_3_1;
STATE USEFIRST ARG2_3_1 :
    MATCH "extern void __VERIFIER_assume(int);" -> GOTO ARG2_4_1;
STATE USEFIRST ARG2_4_1 :
    MATCH "extern void __VERIFIER_assert(int);" -> GOTO ARG2_5_1;
STATE USEFIRST ARG2_5_1 :
    MATCH "int main(void)" -> GOTO ARG2_6_1;
STATE USEFIRST ARG2_6_1 :
    MATCH "" -> GOTO ARG2_7_1;
STATE USEFIRST ARG2_7_1 :
    MATCH "int __retres;" -> GOTO ARG2_8_1;
STATE USEFIRST ARG2_8_1 :
    MATCH "int x = 5;" -> GOTO ARG2_9_1;
STATE USEFIRST ARG2_9_1 :
    MATCH "int y = 6;" -> ASSUME {x == (5);y == (6);} GOTO ARG2;
    TRUE -> STOP;

STATE USEFIRST ARG2 :
    MATCH "__VERIFIER_assert(x == y);" -> GOTO ARG3;
    TRUE -> STOP;

STATE USEFIRST ARG3 :
    MATCH "" -> ASSUME {cond == (0);} GOTO ARG4;
    TRUE -> STOP;

STATE USEFIRST ARG4 :
    MATCH "[!(cond)]" -> ASSUME {cond == (0);} GOTO ARG5;
    TRUE -> STOP;

STATE USEFIRST ARG5 :
    MATCH "ERROR: {abort();}" -> ERROR;
    TRUE -> STOP;

STATE USEFIRST ARG8 :
    TRUE -> STOP;

END AUTOMATON
