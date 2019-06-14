// -*- tab-width:4 ; indent-tabs-mode:nil -*-
//:: cases DuplicateNameJava
//:: tools silicon
//:: verdict Error

public class DuplicateName {
    void test(int abc) {
        while(true) {
            int abc;
        }
    }
}
