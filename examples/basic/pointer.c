// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: case CPointers
//:: tool silicon
//:: verdict Pass


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
    // destroyPermission(&x);
}

/*@
requires \pointer(a, 1);
@*/
void destroyPermission(int *a) {

}

// /*@
// @*/
// void merge(int *left, int leftLen, int *right, int rightLen) {
//
// }
//
// /*@
// requires len > 0;
// context \pointer(data, len);
// @*/
// void sort(int *data, int len) {
//     if(len <= 1) {
//         return;
//     } else {
//         int mid = len / 2;
//         sort(data, mid);
//         sort(&data[mid], len-mid);
//         merge(data, mid, &data[mid], len-mid);
//     }
// }
