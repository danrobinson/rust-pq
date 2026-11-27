import Parallel.KeygenShape

namespace ParallelKeygen.Tree
private def shape0 : Shape := .leaf 1 (0)
private def shape1 : Shape := .branch false (0) (0) shape0 shape0
private def shape2 : Shape := .branch false (0) (0) shape1 shape1
private def shape3 : Shape := .branch false (0) (0) shape2 shape2
private def shape4 : Shape := .branch false (0) (0) shape3 shape3
private def shape5 : Shape := .branch false (0) (0) shape4 shape4
private def shape6 : Shape := .branch false (0) (0) shape5 shape5
private def shape7 : Shape := .branch false (0) (0) shape6 shape6
private def shape8 : Shape := .branch false (0) (0) shape7 shape7
private def shape9 : Shape := .branch false (0) (0) shape8 shape8
private def shape10 : Shape := .leaf 2 (0)
private def shape11 : Shape := .branch false (0) (0) shape10 shape10
private def shape12 : Shape := .leaf 4 (0)
private def shape13 : Shape := .branch true (0) (0) shape12 shape12
private def shape14 : Shape := .branch false (0) (0) shape13 shape13
private def shape15 : Shape := .leaf 8 (0)
private def shape16 : Shape := .branch true (0) (0) shape15 shape15
private def shape17 : Shape := .branch true (0) (0) shape16 shape16
private def shape18 : Shape := .branch false (0) (0) shape17 shape17
private def shape19 : Shape := .branch true (0) (0) shape17 shape17
private def shape20 : Shape := .branch false (0) (0) shape19 shape19
private def shape21 : Shape := .branch true (0) (0) shape19 shape19
private def shape22 : Shape := .branch false (0) (0) shape21 shape21
private def shape23 : Shape := .branch true (0) (0) shape21 shape21
private def shape24 : Shape := .branch false (0) (0) shape23 shape23
private def shape25 : Shape := .branch true (0) (0) shape23 shape23
private def shape26 : Shape := .branch false (0) (0) shape25 shape25
private def shape27 : Shape := .branch true (0) (0) shape25 shape25
private def shape28 : Shape := .branch false (0) (0) shape27 shape27
private def shape29 : Shape := .branch true (0) (0) shape27 shape27
private def shape30 : Shape := .branch false (0) (0) shape29 shape29
def schedule (wide : Bool) : List Shape :=
  if wide then [shape11, shape14, shape18, shape20, shape22, shape24, shape26, shape28, shape30]
  else [shape1, shape2, shape3, shape4, shape5, shape6, shape7, shape8, shape9]
end ParallelKeygen.Tree
