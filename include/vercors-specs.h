
extern void requires_marker();
extern void ensures_marker();
extern void forall_marker();
extern void invariant_marker();
extern void kernel_marker();
extern void barrier_marker();
extern int Perm(void* x, int y);
extern int ArrayPerm(void* x,int ofs,int step, int count, int y);
extern int Old(int old);

#define REQUIRES(arg) for(int i=0;0==0;requires_marker()) arg

#define ENSURES(arg) for(int i=0;0==0;ensures_marker()) arg

#define INVARIANT(arg) for(int sdjbgfjaskdbgjkasdbfjgkbsd=0;0==0;invariant_marker()) arg

#define FORALL(t,x,g,e) for(t x=0;g;forall_marker()) e

#define PERM(x,y) Perm(&x,y)

#define OLD(x) Old(x)

#define ARRAY_PERM(ar,ofs,step,count,frac) ArrayPerm(ar,ofs,step,count,frac)

#define KERNEL(tid,count) for(int tid=0;0==count;kernel_marker())

#define BARRIER for(int sdjbgfjaskdbgjkasdbfjgkbsd=0;0==0;barrier_marker())

