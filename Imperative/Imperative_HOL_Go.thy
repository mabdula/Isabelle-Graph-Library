theory Imperative_HOL_Go
  imports
    "HOL-Imperative_HOL.Imperative_HOL"
    "Go.Go_Setup"
begin

section \<open>Imperative HOL in Go\<close>

text \<open>The Go target of the AFP has no setup for Imperative HOL. A computation of type
  @{typ "'a Heap"} becomes a Go closure \<open>func () A\<close>, an array a Go slice and a reference a
  Go pointer. The array operations depend on the representation of indices and are printed in
  the theory \<open>Code_Target_Machine_Int\<close>, on machine integers.\<close>

code_printing code_module "Heap" \<rightharpoonup> (Go) \<open>
package Heap

func Bind[A, B any](m func() A, f func(A) func() B) func() B {
  return func() B { return f(m())() }
}

func Return[A any](x A) func() A {
  return func() A { return x }
}

func Ref[A any](x A) func() *A {
  return func() *A { r := new(A); *r = x; return r }
}

func Lookup[A any](r *A) func() A {
  return func() A { return *r }
}

func Update[A any](r *A, x A) func() struct{} {
  return func() struct{} { *r = x; return struct{}{} }
}
\<close>
| type_constructor Heap \<rightharpoonup> (Go) "func ()/ _"
| constant bind \<rightharpoonup> (Go) "Heap.Bind( _, _ )"
| constant return \<rightharpoonup> (Go) "Heap.Return( _ )"
| type_constructor array \<rightharpoonup> (Go) "[]_"
| type_constructor ref \<rightharpoonup> (Go) "*_"
| constant ref' \<rightharpoonup> (Go) "Heap.Ref( _ )"
| constant Ref.lookup \<rightharpoonup> (Go) "Heap.Lookup( _ )"
| constant Ref.update \<rightharpoonup> (Go) "Heap.Update( _, _ )"
| type_constructor unit \<rightharpoonup> (Go) "struct{}"
| constant Unity \<rightharpoonup> (Go) "struct{}{}"

code_reserved (Go) Heap

end

