extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "test_locks_8.c", 3, "reach_error"); }

extern int __VERIFIER_nondet_int();
int main()
{
    int p1 = __VERIFIER_nondet_int();  // condition variable
    int lk1; // lock variable

    int p2 = __VERIFIER_nondet_int();  // condition variable
    int lk2; // lock variable

    // int buffer[2000];
    // int * ptr = &(buffer[0]);
    // int i = 0;

    // while(i < 125) {
    while(1) {

        // if (ptr > &buffer[0]+2000) {
        //     goto ERROR;
        // }

        lk1 = 0; // initially lock is open

        lk2 = 0; // initially lock is open

        // lock phase
        if (p1 != 0) {
            lk1 = 1; // acquire lock
        } else {}

        if (p2 != 0) {
            lk2 = 1; // acquire lock
        } else {}

        // if (lk1) {
        //     *ptr = 1;
        //     ptr += 16;
        // }

        // unlock phase
        if (p1 != 0) {
            if (lk1 != 1) goto ERROR; // assertion failure
            lk1 = 0;
        } else {}

        if (p2 != 0) {
            if (lk2 != 1) goto ERROR; // assertion failure
            lk2 = 0;
        } else {}
    }
    ERROR: {reach_error();abort();}
}
