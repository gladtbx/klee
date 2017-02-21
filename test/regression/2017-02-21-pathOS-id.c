// RUN: %llvmgcc %s -emit-llvm -g -O0 -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --output-dir=%t.klee-out -write-paths %t.bc 2> %t.log
// RUN: cat %t.klee-out/test000001.path | wc -l | FileCheck %s
// RUN: cat %t.klee-out/test000002.path | wc -l | FileCheck %s
// RUN: cat %t.klee-out/test000003.path | wc -l | FileCheck %s
// RUN: cat %t.klee-out/test000004.path | wc -l | FileCheck %s
// CHECK: 1
int main(){
	int a, b;
	klee_make_symbolic (&a, sizeof(int), "a");
	klee_make_symbolic (&b, sizeof(int), "b");
	klee_assume(a<2);
	klee_assume(a>=0);
	malloc(a);
	if(b){
		b++;//do something
	}
	return b;
}
