import Parallel.KeygenShape
namespace Shakeopt.ForsTree
open ParallelKeygen.Tree
private def t0 : Shape := .leaf 8 (0)
private def t1 : Shape := .branch true (0) (0) t0 t0
private def t2 : Shape := .branch true (0) (0) t1 t1
private def t3 : Shape := .branch false (0) (0) t2 t2
private def t4 : Shape := .branch true (0) (0) t2 t2
private def t5 : Shape := .branch false (0) (0) t4 t4
private def t6 : Shape := .branch true (0) (0) t4 t4
private def t7 : Shape := .branch false (0) (0) t6 t6
private def t8 : Shape := .branch true (0) (0) t6 t6
private def t9 : Shape := .branch false (0) (0) t8 t8
private def t10 : Shape := .branch true (0) (0) t8 t8
private def t11 : Shape := .branch false (0) (0) t10 t10
private def t12 : Shape := .branch true (0) (0) t10 t10
private def t13 : Shape := .branch false (0) (0) t12 t12
private def t14 : Shape := .branch true (0) (0) t12 t12
private def t15 : Shape := .branch false (0) (0) t14 t14
private def t16 : Shape := .branch true (0) (0) t14 t14
private def t17 : Shape := .branch false (0) (0) t16 t16
private def t18 : Shape := .branch true (0) (0) t16 t16
private def t19 : Shape := .branch false (0) (0) t18 t18
private def t20 : Shape := .branch true (0) (0) t18 t18
private def t21 : Shape := .branch false (0) (0) t20 t20
private def t22 : Shape := .branch true (0) (0) t20 t20
private def t23 : Shape := .branch false (0) (0) t22 t22
private def t24 : Shape := .branch true (0) (0) t22 t22
private def t25 : Shape := .branch false (0) (0) t24 t24
def schedule : List Shape := [t3, t5, t7, t9, t11, t13, t15, t17, t19, t21, t23, t25]
end Shakeopt.ForsTree
