# 現在の状況

数学的ソースは無変更。14モジュールと`ASGinzburg.lean`が旧SHA-256に一致しています。

| 項目 | 今回の結論 |
|---|---|
| lake build | 成功、終了0、3123 jobs |
| 個別公理監査 | 172異なる名前、終了0。初期161宣言＋既存instance 11件 |
| 完成済み補助定理 | 84件。全件が監査対象 |
| sorry / admit / 独自axiom | ソース内0件 |
| 許容公理 | propext、Classical.choice、Quot.soundだけ |
| 禁止依存 | sorryAx、Lean.ofReduceBool、Lean.trustCompilerはなし |
| 数学的主結果 | 定理3.2・系5.2は未証明、形式的な文も未実装 |
| CI | push/pull_requestで固定版のビルド・監査、今回のログをartifactへ保存 |
| 旧版・入力・回収 | checkpoints/とrecovery/、入力PDFを保存 |

最新検証 `20261007T234426Z-5fdb879f`：終了0、12.950793秒。
UTC 2026-10-07T23:44:26.191634+00:00 → 2026-10-07T23:44:39.142436+00:00。
初回の成功検証（キャッシュ準備を含む）は61.159680秒、全段階終了0。

# 形式化状況

2026年10月8日（JST）。数学的範囲は旧版と同じで、主結果の完全形式化は未完成です。

## 検証済みの範囲

| 論文中の位置 | Leanファイル | 実装・証明済み | 残る範囲 |
|---|---|---|---|
| §1.1、(1.1) | `CutQuiver.lean` | cut箙、被覆頂点、heightの全単射、正のwinding、pathの次数公式 | 被覆道代数をZ-代数として束ねる同定 |
| §1.1の巡回空間 | `CutPotential.lean` | 回転商の自由ベクトル空間、cut次数、唯一のcutの分割とnormal form | 閉じた可合成道の部分空間とkQ/[kQ,kQ]の同定 |
| (3.8) | `CyclicDerivative.lean` | 巡回微分の実装、回転不変性、cut復元恒等式 | Jacobianイデアルおよび商代数との接続 |
| 道代数 | `PathAlgebra.lean` | 成分の自由ベクトル空間、双線形積、単位元、結合則 | 関係イデアルとその商、unrolling |
| (1.4) | `ZAlgebra.lean` | 具体的な成分、双線形な積、局所単位元、connected・positive・finite条件 | 原論文のAS正則性の定義 |
| 命題1.2の帰納法 | `ZAlgebra.lean` | 成分が生成元と短い積に分解されれば全成分を生成する | 分解条件を最小射影分解から導くこと、核が矢イデアルの二乗に入ること |
| (1.5) | `Representables.lean` | k線形圏と右線形presheaf、YonedaのHom同型、逆向きHomの消滅、自己Homの次元1 | 加群圏のAbelian・射影性、単純加群 |
| 命題1.3の数値段階 | `ExtDimension.lean` | 有限台の自然数次元表の総和1と非零項1からdelta形を導く | 表と実際のExtの同定、有限台、非零項の導出 |
| 命題1.3のtop Hom計算 | `TopCohomology.lean` | 前の空間が零ならtop cokernelはそのまま、値域kなら次元1 | 実際のHom複体とExtへの同定 |
| 命題1.4の貼り合わせ | `WindowPeriodicity.lean` | coherentな区間同型から積と単位元を保つ周期同型を構成 | D Ext³から区間同型を作る部分全体 |
| 命題3.1の共役段階 | `Conjugation.lean` | 完全忠実な線形関手と対象同型から、積を保つHom線形同型を構成 | tilting、Serre functor、高次preprojectiveとの同定 |
| §4、§5の数値計算 | `Hilbert.lean` | 一般の正のlagの漸化式の一意性、quadratic Hilbert値、増大上界 | exact resolutionからのEuler式、del Pezzo模型との幾何的比較 |
| 系5.2の線形表示 | `Tensor333.lean` | 実際の三重テンソル積、係数表示、cut関係への同型、27次元、基底変更 | tensor・potential・Jacobian代数の完全な比較 |
| 系5.2の箙 | `Triangle333.lean` | 三角形箙、全矢のwinding=1、cut次数1閉路の長さ3、明示的potentialのcut恒等式 | 箙自己同型とGL(X)×GL(Y)×GL(Z)の群・商の同定 |
| (1.3)の次数 | `GinzburgGrading.lean` | a、a*、t_vの型と三つの次数、windingの正値性、loop項の次数 | dg代数、d²=0、コホモロジー、Ginzburg正則性 |

## 主結果の状態

| 主張 | 状態 |
|---|---|
| 定理3.2：一般の型QのAS–Ginzburg対応 | **未証明。Leanの形式的な文も未実装。** |
| 命題1.4：AS条件からの周期性 | **未証明。区間同型を仮定した最後の貼り合わせのみ証明。** |
| 命題5.1：quadratic AS正則Z-代数の三周期性 | **未証明。** |
| 系5.2：(3,3,3)型の全単射 | **未証明。Leanの形式的な文も未実装。** |

完成した補題は84件です。`verification/declarations.json`に初期161宣言と既存instance 11件の全172監査対象を列挙しています。
補題の本来の仮定はソースの型を参照して下さい。
特に`WindowSystem.isPeriodic`は`WindowSystem`を入力に持ち、AS条件からの周期性ではありません。

## 検査と残存事項

- 初期161宣言の一覧は`recovery/corrected_declarations.json`とも一致。161異なる名前を確認。
- `InWindow.mono`の完全名を監査。ソース・コマンド・ログの各重複を拒否。
- 回帰テスト10件が成功。監査漏れ、重複、禁止公理、旧成功文字列による誤判定を検査。
- 14数学モジュール＋ルートimportの同一性、旧verification/保存のSHA-256照合が成功。
- 固定Leanの実行版とmanifestの全依存checkoutを検査。最新runの環境・ログ・終了コードで判定。
- 既存の未使用変数・simp引数のlint警告は残存。コンパイルエラーはなし。
- GitHubへの保存とActionsの実行状況は`RECENT_RUN.md`参照。

数学的形式化の再開は別の明示的指示が必要です。未証明の主結果を隠す公理・追加クラスはありません。
