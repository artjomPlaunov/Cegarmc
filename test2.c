int main () {
    int x=6;
    int y=6;
    /*@ assert x == y;*/
    if (x == y) {
        int y = 6;
    } else {
        int y = 7;
    }
}