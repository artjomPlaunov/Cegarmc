int main () {
    int x;
    /*@ assert x == 100;*/
    if (x == 1) {
        int y = 6;
    } else {
        int y = 7;
    }
}