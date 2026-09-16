# 继续形式化时补充的证明细节

本文档记录从原稿到 Lean 证明所需的展开步骤。完成状态以实际编译为准，
不能用本文档替代 Lean 定理。A–N 均已通过 Lean 检查；6593 条证书记录已经全部内核验证，
最终主定理、完整等号分类和实指数 λ≥2 的推论均不含未证明的输入。

## A：中心化余项

先对任意中心化族 `w : Fin m → ℂ`、`sum w = 0` 证明

```
sum |D-c*w_j|² = m*|D|² + c²*sum |w_j|².
```

这个恒等式给出整个插值路径 `D-c*theta*w_j` 的统一二阶矩上界，
不需要任何单个因子非零。删去一个因子的 AM–GM 界则来自

```
(m/(m-1))^(m-1) ≤ exp(1) < (5/3)².
```

对多项式 `P(theta) = product(D-c*theta*w_j)` 使用已经证明的无除法微分恒等式，
先对导数取范数，再用实区间上的微积分基本定理积分。唯一需要除以的量为 `|D|`。
令 `D=1-at*mean(q)` 后，由 `|mean(q)|≤1`、`0≤at<1` 得到 `D≠0`。
积分 `theta` 所产生的 `1/2` 把 `5/3` 变为 `5/6`。

对应：`DeletedProducts.lean`、`CenteredRemainder.lean`。

## B：中心化标量不等式

将原稿对中心幂的积分公式写成无除法形式：

```
b*(m+1)*integral_0^1 (1-b*t)^m dt = 1-(1-b)^(m+1).
```

因此该步骤不需要假设均值非零。由 `Re(D)≤|D|` 和 `1-a*x*t>0` 控制分母，
由 `beta_s≤beta` 控制幂，再结合第一原点通道的范数上界，得到所需标量不等式。
`centered_scalar_inequality` 的原点积分界是明确前提，后续需要从实际多项式的
通信恒等式导入它。

对应：`CenteredScalar.lean`。

## C：直接标量不等式

从已证明的多项式微分恒等式，经求值和区间积分得到完整微分原点恒等式。
余项使用 A 中删去一个因子的估计和 `sum |q_j|²≤m`。
第一原点通道给出 `|integral F|≤1/(m+1)`，得到原稿中的 `m*a/(m+1)`。

对应：`DirectScalar.lean`。

## D：抽象矩形排除

把实际标量 `C,E,F,R,T` 与矩形上界分开。对所有 `0≤r≤1`，
`a*r+C*r*(1-r²)` 随 `a,C` 单调。数值检查只要证明四种测试中的任意一种，
并提供全部上界的正确性，即可排除整个矩形。边界测试明确需要对
`E/(1-a²)` 的统一上界，不能只用一个固定的 `E` 上界替代。

对应：`RectangleExclusion.lean`。

## E：商函数凸性的代数证明

对于 `u,v≥0` 和 `d,e>0`，当 `u*d+v*e>0` 时，

```
(u*x+v*y)²/(u*d+v*e) ≤ u*x²/d + v*y²/e.
```

两边清分母后的差正是 `u*v*(e*x-d*y)²`。如果非负函数 `f` 凸，
而 `g` 为正仿射函数，就得到 `f²/g` 凸。
取 `f=b^(r/2)`，用 `r≥2` 和非负凸二次函数 `b` 的复合凸性，
推出 `b^r/(1-d*t)` 凸。这避免了在 `b=0` 处单独处理二阶导数。

带权求积界通过把弦函数乘以 `t` 或 `t²`，精确积分三次多项式而得。
Lean 得到的权重与原稿完全一致。

对应：`ConvexQuadrature.lean`。

## F–J：舍入、单条记录和覆盖

`DyadicSoundness.lean` 证明 160 位定点网格上的上下舍入、二分幂、平方根以及半整数幂包围。
`RectangleGap.lean` 和 `RectangleBounds.lean` 分别证明极坐标间隙测试和矩形上的函数包围。
`BoundaryTail.lean` 证明边界测试使用的幂函数商的单调性。
`FiniteQuadrature.lean` 证明相邻区间积分相加后的整个求积网格误差界。
`CertificateVerifier.lean` 中 `one_record_verifier_sound` 和 `verifyRecord_sound` 已通过检查。
`CertificateCoverage.lean` 证明次数块与参数区间相接时的完整覆盖。

原始 JSON 已逐字节保存为 `verification/certificate.json`，SHA-256 为
`8384d62a377b4fcac4080d0e05979d7a6fcf90437b7e4911927a5403d4052709`。
`Certificate/Data.lean` 保存全部 6593 条记录；`Certificate/DataFacts.lean` 已经内核验证
6593 条记录、430 个次数块和完整覆盖。逐条排除检查由 `decide +kernel` 完成，43 个批次均已通过。
为使内核可以直接求值，网格使用结构递归的插入排序。

## 大次数分析补充

`ScalarBridge.lean` 已证明实际多项式反例会给出 `ScalarConditions`，包括第一原点积分界。
`ExponentialIntegrals.lean` 通过显式原函数证明两个指数积分界；
其逐点分解同时适用于 beta 的极小点落在区间外的情况。
`LogGrowth.lean` 由 log(u) ≤ u−1 得到整个半无限次数范围的对数增长界。
`NearPowerTails.lean` 和 `NearEndpointBounds.lean` 已完成近边界幂尾与端点项估计。
`LargeNear.lean` 已证明近边界大次数排除。这里放宽系数界为 `6001/m`；
在 `m≥1000000` 下仍严格小于 `a/2`，所以保留原稿结论。

远离边界的分析已经完成。对 `a≥1/2`，采用 delta 的三个区间
`[1/10,1/2]`、`[1/2,5/8]`、`[5/8,3/4]`，用指数 `7/4`、`3/2`、`21/16`
给出较宽但充分的余项界；这些有理幂常数已在 `PowerTailBounds.lean` 检查。
这避免使用原稿中更尖锐的辅助函数单调性，仍覆盖全部参数。

`AwayScalarBounds.lean` 把积分拆成指数衰减部分与端点幂项。
`AwayIncreasingBounds.lean` 分别处理小 a 和大 a 的幂项，
`LargeAway.lean` 在两种情况下给出直接标量不等式的矛盾。
`LargeDegreeResult.large_degree_interior` 已无条件证明全部 `n≥1000001`。

`Certificate/Verified.lean` 汇总全部记录的内核证明。`FinalAssembly.lean` 连接有限与无限次数，
`MainTheorem.lean` 给出无证书假设的 K、M、N 和完整等号分类及幂次推论。
部分证书批次使用独立的纯计算命名空间以减少内存；`CertificateKernel/Bridge.lean`
证明其对每个输入与原验证器相同，`CertificateKernel/Tagged.lean` 证明选定测试的充分性。
