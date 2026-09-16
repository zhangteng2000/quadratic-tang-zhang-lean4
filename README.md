# Quadratic Tang–Zhang：Lean 4 形式化

本工程形式化了《Beyond Sendov's conjecture: the quadratic Tang–Zhang inequality》的
主定理、完整等号分类，以及所有实指数 `λ ≥ 2` 的推论。

设复多项式 `p` 的次数为 `n ≥ 2`，全部零点位于闭单位圆盘。对每个零点 `a`，
临界点 `ζ₁,…,ζₙ₋₁` 按重数计，则

\[
\sum_{j=1}^{n-1}\frac{1}{|a-\zeta_j|^2}\ge n-1.
\]

等号成立当且仅当 `p(z)=c(zⁿ−ω)`，其中 `c ≠ 0`、`|ω|=1`。
分母为零的项在 `ENNReal` 中表示为正无穷。`criticalEnergy` 使用临界点的多重集，
因此保留了全部重数。

## 定理入口

所有名称位于 `QuadraticTangZhang` 命名空间，见
[`MainTheorem.lean`](QuadraticTangZhang/MainTheorem.lean)。

| 定理 | 结论 |
|---|---|
| `mainStatement : MainStatement` | 任意次数的二次 Tang–Zhang 不等式 |
| `equalityStatement : EqualityStatement` | 任意次数的完整等号充要条件 |
| `main_theorem` | 同时给出二次不等式和等号分类 |
| `strict_interior` | 任意复内点零处的严格不等式 |
| `powers_ge_two` | 每个实指数 `λ ≥ 2` 的不等式及等号分类 |
| `remainingInterior : RemainingInteriorStatement` | 次数至少 6 的归一化内点结论 |

这些最终定理不要求用户额外提供证书接受假设或内点结论。
`reciprocalEnergy_rpow` 证明幂次能量定义等于通常的 `1/|a−ζ|^λ`。

## A–N 对应关系

| 阶段 | 主要文件 / 定理 |
|---|---|
| A | `CenteredRemainder.lean`：`centered_remainder_estimate` |
| B | `CenteredScalar.lean`：`centered_scalar_inequality` |
| C | `DirectScalar.lean`：`direct_scalar_inequality` |
| D | `RectangleExclusion.lean`：`abstract_rectangle_exclusion` |
| E | `ConvexQuadrature.lean`、`FiniteQuadrature.lean`：凸性与完整网格求积界 |
| F | `DyadicSoundness.lean`：`halfPower_sound` 及上下舍入正确性 |
| G | `CertificateVerifier.lean`：`one_record_verifier_sound`、`verifyRecord_sound` |
| H | `CertificateCoverage.lean`：`certificate_coverage_sound` |
| I | `Certificate/Data.lean`、`DataFacts.lean`：6593 条记录、430 个次数块 |
| J | `Certificate/Verified.lean`：`full_certificate_evaluates_successfully` |
| K | `MainTheorem.lean`：`finite_degree_interior`，`6 ≤ n ≤ 1000000` |
| L | `LargeDegreeResult.lean`：`large_degree_interior`，`n ≥ 1000001` |
| M | `MainTheorem.lean`：`remainingInterior` |
| N | `MainTheorem.lean`：`mainStatement` |

`ScalarBridge.lean` 从真实多项式反例推导全部标量条件。
`FinalAssembly.lean` 连接有限与无限次数区间；低次数、原点、单位圆边界、旋转和等号分类
由其他已证明模块提供。形式化时补充的数学细节见 [`PROOF-NOTES.md`](PROOF-NOTES.md)。

## 证书与信任范围

原始输入是 `verification/certificate.json`，SHA-256：

```
8384d62a377b4fcac4080d0e05979d7a6fcf90437b7e4911927a5403d4052709
```

坐标为精确的 100 位二进制定点数；幂、平方根和商的包围使用 160 位网格。
全部计算在整数和有理数上进行。Lean 验证器检查参数约束、间隙估计、求积网格和排除测试；
覆盖定理把相邻参数区间与次数块连接起来。

每条记录的数值证明使用 `decide +kernel`。部分批次通过只导入计算定义的
`CertificateKernel` 模块检查；`CertificateKernel/Bridge.lean` 证明它与原验证器对每个输入
完全一致。原始验证器的最终接受命题仍在 `Certificate/Verified.lean` 中证明。
`CertificateKernel/Tagged.lean` 证明按标签选择充分的排除测试也会被原验证器接受。

最终公理审计只包含 `propext`、`Classical.choice`、`Quot.sound`。
工程没有使用 `sorry`、`admit`、新增公理或 `native_decide`。
Python 脚本负责编码与调度，其运行结果不充当 Lean 证明。

## 复现

固定 Lean `v4.34.0-rc1`；mathlib 提交
`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`。其余依赖见 `lake-manifest.json`。

首次安装依赖后运行：

```powershell
lake exe cache get
.\verify.ps1
```

`verify.ps1` 按批次构建证书，再构建最终主定理并检查公理。
从零计算全部证书可能需要数小时；已有的成功构建会被 Lake 复用。
也可使用 `python verification/build_certificate_proofs.py` 以受限并发预构建证书。

结果见 `verification/build.log`、`verification/axioms.log`、`verification/summary.json`。
`verification/source-sha256.json` 记录交付源文件的哈希。
`python verification/check_encoding.py` 可核对两份 Lean 数据的全部整数、430 个次数块及其记录引用。

## 来源

通信恒等式及部分辅助结论复用了 [teorth/sendov](https://github.com/teorth/sendov)
中完整的 Lean 证明。固定提交、改动范围和 Apache-2.0 许可见
`vendor/PROVENANCE.md` 与 `vendor/LICENSE.sendov`。
