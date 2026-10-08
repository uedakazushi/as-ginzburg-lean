# 回収時点の状況

Leanソースは変更していません。最後の成功チェックポイントと全16ソースのハッシュが一致しています。
現在のプロジェクト場所と検査記録はHANDOFF.mdを参照してください。

| 項目 | 回収時点の結論 |
|---|---|
| 現在のlake build | 実行不能。終了127、lake: command not found |
| 最後の成功 | 2026-10-07 08:37:54.907799 UTC、3123 jobs成功 |
| 完成済み宣言 | def 55、theorem 84、abbrev 14、structure 6、inductive 2。全名はDECLARATIONS.md |
| sorry / admit / 独自axiom | プロジェクトLeanソース内0件。残存箇所なし |
| 非コンパイルファイル | 最後の成功時にはなし。現在は環境欠落のためファイル単位の再検証不能 |
| 個別公理監査の不足 | InWindow.monoが一覧生成時に誤記され、監査対象から欠落 |
| 全ファイル | 元zipの35ファイル。全件はFILES.md。削除済み一時ファイルの一覧は不明 |

以下の表は最後の成功時点に実装された数学的範囲です。現在の再ビルド成功を意味しません。

# 形式化状況

2026年10月7日。主結果の完全形式化は未完成です。

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

完成した補題は84件です。`verification/declarations.json`に全宣言を列挙しています。
補題の本来の仮定はソースの型を参照して下さい。
特に`WindowSystem.isPeriodic`は`WindowSystem`を入力に持ち、AS条件からの周期性ではありません。

## 検査

- 全14モジュールと全宣言のaudit targetを含む`lake build`：成功。
- sourceの`sorry`、`admit`、独自`axiom`：0件。
- 161監査コマンド・160異なる宣言名の`#print axioms`：標準の`propext`、`Classical.choice`、`Quot.sound`の範囲。`InWindow.mono`の個別監査は欠落。
- `sorryAx`、`Lean.ofReduceBool`、`Lean.trustCompiler`：依存なし。
- 最後の成功時点でコンパイルしないプロジェクト内Leanファイル：なし。現在はlakeがなく再検証不能。

未証明の主結果を隠すための公理・追加クラスはありません。
それらは`GAPS.md`で未実装の作業として列挙しています。
