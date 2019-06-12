void test() {
    int x = 0;
    int *y = &x;
    returnPointer(y);
}

int *returnPointer(int *x) {
    return x;
}
