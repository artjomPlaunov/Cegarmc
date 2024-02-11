int main () {
    int x = 1;
    /*@ assert 1 == 1;*/
    if (x == 1) {
        int y = 6;
    } else {
        int y = 7;
    }
}