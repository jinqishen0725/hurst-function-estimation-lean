事件:13:45 检查点使用了可预测的 /tmp 日志路径,被各路 agent 的后续编译覆盖(A/C 现为 A_EXIT:1/C_EXIT:1 = 其中问中间态)。
保留:本目录两个 session-exec 标准输出副本,记录当时 Lean 真实退出码 A_EXIT:0 / C_EXIT:0。
教训:检查点一律使用 verification/checkpoints/<UTC>-<track>/ 专属目录 + 源码快照 + sha256。
