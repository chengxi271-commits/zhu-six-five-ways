# 论主等于六：五路证明

Lean 4 formal artifact for **论主等于六：基于阿奎那五路证明与 Lean 4 形式验证的第一算术本原考辨**。

## 证明与复现

五路论证分别由 `ViaMotion`、`ViaCause`、`ViaNecessity`、`ViaDegree`、`ViaPurpose` 给出条件，导出同一自然数参数等于六。源码还包含五路充要关系、共同存在实例及候选数辨析。

环境：**Lean 4.34.1**，仅使用自带 `Std`，不依赖 mathlib。

```sh
cd lean
lean -j 2 Main.lean
```

完整验证全部定理及公理依赖，从仓库根目录运行：

```sh
python scripts/verify.py --lean /path/to/lean
```

Python 脚本只依赖标准库。运行结果写入 `evidence/`。`Audit.lean` 是脚本生成的逐一定理检查文件，不是另一套证明。

本地核验：20 条定理通过，五个主定理均有内核检查的证明项，无 `sorry`、自定义公理或 `native_decide`。标准公理依赖见 `evidence/verification.json`。

## 目录

- `lean/Main.lean`：正式证明源码。
- `lean/lean-toolchain`：固定工具链版本。
- `scripts/verify.py`：验证与结果导出。
- `evidence/lean-validation.log`：实际核验输出。
- `evidence/verification.json`：定理依赖和候选数数据。

论文署名采用匿名作者；工具参与说明见最终稿。此仓库的公开不表示期刊录用或发表。
