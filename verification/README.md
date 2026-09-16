# 验证记录

`summary.json` 记录全部 A–N 以及等号、幂次推论的成功验证；`build.log` 和 `axioms.log` 是最终构建与公理审计日志。

`certificate-kernel/Checked00.log` 至 `Checked42.log` 对应全部 43 批；其中的成功缓存复用来自此前已完成的 Lean 内核计算。

`encoding.json` 核对原始证书与两份 Lean 数据的 6593 条整数记录及全部 430 个次数块。`source-sha256.json` 记录交付源文件哈希。

在项目根目录运行 `./verify.ps1` 可以重新构建并执行公理审计。
