// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases vector-add-c
//:: tools silicon
//:: verdict Pass
/*@
  requires \length(a)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  requires \length(b)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(b[i],1/2));
  requires \length(c)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(c[i],1/2));

  ensures  \length(a)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(a[i],write));
  ensures  \length(b)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(b[i],1/2));
  ensures  \length(c)==len ** (\forall* int i ; 0 <= i && i < len ; Perm(c[i],1/2));

  ensures  (\forall int i ; 0 <= i && i < len ; a[i]==b[i]+c[i]);
  ensures  (\forall int i ; 0 <= i && i < len ; b[i]==\old(b[i]));
  ensures  (\forall int i ; 0 <= i && i < len ; c[i]==\old(c[i]));
@*/
void vector_add(int a[],int b[],int c[],int len){  
  for(int i=0;i < len;i++)
  /*@
    requires \length(a)==len ** Perm(a[i],write);
    requires \length(b)==len ** Perm(b[i],1/2);
    requires \length(c)==len ** Perm(c[i],1/2);

    ensures  \length(a)==len ** Perm(a[i],write);
    ensures  \length(b)==len ** Perm(b[i],1/2);
    ensures  \length(c)==len ** Perm(c[i],1/2);
    
    ensures  b[i]==\old(b[i]);
    ensures  c[i]==\old(c[i]);
    ensures  a[i]==b[i]+c[i];
  @*/
  {
    a[i]=b[i]+c[i];
  }
}
