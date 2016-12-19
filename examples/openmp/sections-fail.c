// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: case OpenMPSectionFail1
//:: tools silicon
//:: verdict fail
/*
 * Demonstrates how two loops that must be fused to be 
 * data race free can be specified and verified.
 */
#include <stdio.h>
#include <omp.h>

/*@
  invariant a != NULL && b != NULL && c != NULL;
  invariant len>0 && \length(a)==len && \length(b)==len && \length(c)==len;
  context   (\forall* int k;0 <= k && k < len ; Perm(a[k],1/4));
  context   (\forall* int k;0 <= k && k < len ; Perm(b[k],1/4));
  context   (\forall* int k;0 <= k && k < len ; Perm(c[k],1));
  ensures   (\forall  int k;0 <= k && k < len ; c[k]==a[k]+b[k]);
@*/
void add(int len,int a[],int b[],int c[]){
  #pragma omp parallel
  {
    /*@
      context (\forall* int k;0 <= k && k < len ; Perm(a[k],1/4));
      context (\forall* int k;0 <= k && k < len ; Perm(b[k],1/4));
      context (\forall* int k;0 <= k && k < len ; Perm(c[k],1));
      ensures (\forall  int k;0 <= k && k < len ; c[k]==a[k]+b[k]);
    @*/
    #pragma omp for schedule(static) nowait
    for(int i=0;i<len;i++)
    /*@
      context Perm(c[i],1) ** Perm(a[i],1/4);
      ensures c[i] == a[i];
    @*/
    {
      c[i]=a[i];
    }
    #pragma omp for schedule(static)
    for(int i=0;i<len;i++)
    /*@
      context Perm(c[i],1) ** Perm(b[i],1/4);
      ensures c[i] == \old(c[i]) + b[i];
    @*/
    {
      c[i]=c[i]+b[i];
    }
  }
}

/*@
  invariant a != NULL && b != NULL && d != NULL;
  invariant len>0 && \length(a)==len && \length(b)==len && \length(d)==len;
  context   (\forall* int k;0 <= k && k < len ; Perm(a[k],1/4));
  context   (\forall* int k;0 <= k && k < len ; Perm(b[k],1/4));
  context   (\forall* int k;0 <= k && k < len ; Perm(d[k],1));
  ensures   (\forall  int k;0 <= k && k < len ; d[k]==a[k]*b[k]);
@*/
void mul(int len,int a[],int b[],int d[]){
  #pragma omp parallel
  {
    /*@
      context (\forall* int k;0 <= k && k < len ; Perm(a[k],1/4));
      context (\forall* int k;0 <= k && k < len ; Perm(b[k],1/4));
      context (\forall* int k;0 <= k && k < len ; Perm(d[k],1));
      ensures (\forall  int k;0 <= k && k < len ; d[k]==a[k]*b[k]);
    @*/
    #pragma omp for schedule(static) nowait
    for(int i=0;i<len;i++)
    /*@
      context Perm(d[i],1) ** Perm(a[i],1/2);
      ensures d[i] == a[i];
    @*/
    {
      d[i]=a[i];
    }
    #pragma omp for schedule(static)
    for(int i=0;i<len;i++)
    /*@
      context Perm(d[i],1) ** Perm(b[i],1/4);
      ensures d[i] == \old(d[i]) * b[i];
    @*/
    {
      d[i]=d[i]*b[i];
    }
  }
}

/*@
  invariant a != NULL && b != NULL && c != NULL && d != NULL;
  invariant len>0 && \length(a)==len && \length(b)==len && \length(c)==len && \length(d)==len;
  context   (\forall* int k;0 <= k && k < len ; Perm(a[k],1/2));
  context   (\forall* int k;0 <= k && k < len ; Perm(b[k],1/2));
  context   (\forall* int k;0 <= k && k < len ; Perm(c[k],1));
  context   (\forall* int k;0 <= k && k < len ; Perm(d[k],1));
  ensures   (\forall  int k;0 <= k && k < len ; c[k]==a[k]+b[k]);
  ensures   (\forall  int k;0 <= k && k < len ; d[k]==a[k]*b[k]);
@*/
void addmul(int len,int a[],int b[],int c[], int d[])
{
#pragma omp parallel 
{
/*@
  context   (\forall* int k;0 <= k && k < len ; Perm(a[k],1/2));
  context   (\forall* int k;0 <= k && k < len ; Perm(b[k],1/2));
  context   (\forall* int k;0 <= k && k < len ; Perm(c[k],1));
  context   (\forall* int k;0 <= k && k < len ; Perm(d[k],1));
  ensures   (\forall  int k;0 <= k && k < len ; c[k]==a[k]+b[k]);
 ensures   (\forall  int k;0 <= k && k < len ; d[k]==a[k]*b[k]);
@*/
#pragma omp sections 
{
#pragma omp section
   /*@
  context   (\forall* int k;0 <= k && k < len ; Perm(a[k],1/4));
  context   (\forall* int k;0 <= k && k < len ; Perm(b[k],1/4));
  context   (\forall* int k;0 <= k && k < len ; Perm(c[k],1));
  ensures   (\forall  int k;0 <= k && k < len ; c[k]==a[k]+b[k]);
    @*/
  {add(len,a,b,c);}
#pragma omp section
  /*@
  context   (\forall* int k;0 <= k && k < len ; Perm(a[k],1/4));
  context   (\forall* int k;0 <= k && k < len ; Perm(b[k],1/4));
  context   (\forall* int k;0 <= k && k < len ; Perm(d[k],1));
  ensures   (\forall  int k;0 <= k && k < len ; d[k]==a[k]*b[k]);
  @*/
  {mul(len,a,b,d);}
}
}
}

//@ requires false;
int main(int argc, char *argv[]){
  int a[]={1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};
  int b[]={1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};
  int c[]={-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16};
  int d[]={-1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16};


  int i;
  
  printf("a: ");
  for(i=0;i<16;i++){printf("%4d",a[i]);}
  printf("\n");
  printf("b: ");
  for(i=0;i<16;i++){printf("%4d",b[i]);}
  printf("\n");
  
  addmul(16,a,b,c,d);

  printf("c: ");
  for(i=0;i<16;i++){printf("%4d",c[i]);}
  printf("\n");

 printf("d: ");
  for(i=0;i<16;i++){printf("%4d",d[i]);}
  printf("\n");

}


