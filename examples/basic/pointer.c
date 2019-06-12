void test() {
    int x = 0;
    int *y = &x;
    returnPointer(y);
}

int *returnPointer(int *x) {
    return x;
}

/*@
context \pointer(location, 1);
ensures location[0] == 1;
@*/
void setOne(int *location) {
    *location = 1;
}

/*@
ensures \result == 1;
@*/
int returnsOne() {
    int result;
    setOne(&result);
    // destroyPermission(&result);
    return result;
}

void destroyArgument(int x) {
    destroyPermission(&x);
}

/*@
requires \pointer(a, 1);
@*/
void destroyPermission(int *a) {

}

// void arrayPointers() {
//     int x[4];
//     destroyPermission(&x[0]);
// }
