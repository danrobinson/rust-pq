import Parallel.KeygenShape

namespace ParallelFusedSignature
open ParallelKeygen.Tree
private def shape0 : Shape := .leaf 8 (0)
private def shape1 : Shape := .branch true (0) (0) shape0 shape0
private def shape2 : Shape := .branch false (0) (0) shape1 shape1
private def shape3 : Shape := .branch true (0) (0) shape1 shape1
private def shape4 : Shape := .branch false (0) (0) shape3 shape3
private def shape5 : Shape := .branch true (0) (0) shape3 shape3
private def shape6 : Shape := .branch false (0) (0) shape5 shape5
private def shape7 : Shape := .branch true (0) (0) shape5 shape5
private def shape8 : Shape := .branch false (0) (0) shape7 shape7
private def shape9 : Shape := .branch true (0) (0) shape7 shape7
private def shape10 : Shape := .branch false (0) (0) shape9 shape9
private def shape11 : Shape := .branch true (0) (0) shape9 shape9
private def shape12 : Shape := .branch false (0) (0) shape11 shape11
private def shape13 : Shape := .branch true (0) (0) shape11 shape11
private def shape14 : Shape := .branch false (0) (0) shape13 shape13
def schedule : List Shape := [shape0, shape1, shape2, shape4, shape6, shape8, shape10, shape12, shape14]
end ParallelFusedSignature
