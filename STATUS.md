# 現在の状況

既存14数学モジュールは無変更・旧SHA-256一致。新規2モジュールで既存RightModuleの
Abelian構造と成分ホモロジー・exactnessへの接続を完成しました。ルートimportと生成監査を更新。

| 項目 | 今回の結論 |
|---|---|
| lake build | 成功、終了0、3199 jobs |
| 個別公理監査 | 208異なる名前、終了0。全明示的宣言・25 named instanceを含む |
| 完成済み補助定理 | 99件。全件が監査対象 |
| sorry / admit / 独自axiom | ソース内0件 |
| 許容公理 | propext、Classical.choice、Quot.soundだけ |
| 禁止依存 | sorryAx、Lean.ofReduceBool、Lean.trustCompilerはなし |
| 数学的主結果 | 定理3.2・系5.2は未証明、形式的な文も未実装 |
| CI | push/pull_requestで固定版のビルド・監査、今回のログをartifactへ保存 |
| 旧版・入力・回収 | checkpoints/とrecovery/、入力PDFを保存 |

最新ローカル検証 `20261008T003239Z-336ff83a`：終了0、39.289198秒。
UTC 2026-10-08T00:32:39.439384+00:00 → 2026-10-08T00:33:18.728587+00:00。
全段階（11回帰テスト、ソース監査、固定環境、lake build、#print axioms、照合）は終了0。

# 形式化状況

2026年10月8日（JST）。ユーザーの明示的な指示によりRightModuleの形式化を再開。主結果の完全形式化は未完成です。

## 検証済みの範囲

| 論文中の位置 | Leanファイル | 実装・証明済み | 残る範囲 |
|---|---|---|---|
| §1.1、(1.1) | `CutQuiver.lean` | cut箙、被覆頂点、heightの全単射、正のwinding、pathの次数公式 | 被覆道代数をZ-代数として束ねる同定 |
| §1.1の巡回空間 | `CutPotential.lean` | 回転商の自由ベクトル空間、cut次数、唯一のcutの分割とnormal form | 閉じた可合成道の部分空間とkQ/[kQ,kQ]の同定 |
| (3.8) | `CyclicDerivative.lean` | 巡回微分の実装、回転不変性、cut復元恒等式 | Jacobianイデアルおよび商代数との接続 |
| 道代数 | `PathAlgebra.lean` | 成分の自由ベクトル空間、双線形積、単位元、結合則 | 関係イデアルとその商、unrolling |
| (1.4) | `ZAlgebra.lean` | 具体的な成分、双線形な積、局所単位元、connected・positive・finite条件 | 原論文のAS正則性の定義 |
| 命題1.2の帰納法 | `ZAlgebra.lean` | 成分が生成元と短い積に分解されれば全成分を生成する | 分解条件を最小射影分解から導くこと、核が矢イデアルの二乗に入ること |
| (1.5) | `Representables.lean` | k線形圏と右線形presheaf、YonedaのHom同型、逆向きHomの消滅、自己Homの次元1 | 単純加群、直和・局所単位元付き加群との明示的同値 |
| §1.2の加群圏・(1.6)の基盤 | `RightModuleAbelian.lean`、`RightModuleHomology.lean` | (余)極限の閉性、Abelian構造、核・余核・homologyの成分同型、exactness・短完全列・mono/epiの成分判定 | 実際の射影分解・minimality・Extとの比較 |
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

完成した補題は99件です。`verification/declarations.json`に初期161宣言を含む全208監査対象を列挙しています。
新規単位は12 theorem・4 def・14 named instance。既存RightModuleの定義を保ち、
周期性・Ext同型・AS結論を仮定に追加していません。
補題の本来の仮定はソースの型を参照して下さい。
特に`WindowSystem.isPeriodic`は`WindowSystem`を入力に持ち、AS条件からの周期性ではありません。

## 検査と残存事項

- 初期161宣言の一覧は`recovery/corrected_declarations.json`とも一致。161異なる名前を確認。
- `InWindow.mono`の完全名を監査。ソース・コマンド・ログの各重複を拒否。
- 回帰テスト11件が成功。監査漏れ、重複、禁止公理、旧成功文字列による誤判定を検査。
- 既存14数学モジュールとPDFの同一性を再確認。新規2モジュールとroot import追加は意図した差分。
  旧verification/保存、recovery/は無変更。
- 固定Leanの実行版とmanifestの全依存checkoutを検査。最新runの環境・ログ・終了コードで判定。
- 既存の未使用変数・simp引数のlint警告は残存。コンパイルエラーはなし。
- GitHubへの保存とActionsの実行状況は`RECENT_RUN.md`参照。

今回のRightModuleの目標を超える数学的形式化には別の明示的指示が必要です。未証明の主結果を隠す公理・追加クラスはありません。

原論文の`Gr(A)`との明示的な直和加群モデルの同値、radical・s_v、
(1.6)の完全・最小分解、(1.7)の実際のExt条件は未実装です。
今回の形状の(余)極限存在の仮定は有限図式についてmathlibで満たされます。
ASから導出すべき新たな仮定を置いた条件付き補題は追加していません。

最新CIとリモート保存状況はRECENT_RUN.mdを参照してください。

数学的実装コミットf8e7ce0のpush・pull_request CIは双方success、各12ファイルのartifact保存を確認。
詳細はRECENT_RUN.mdとverification/rightmodule_github_ci_evidence.json。

射影性：RightModuleProjectives.leanで全右加群に対する線形Yoneda同型とProjectiveを完成。
最新の検証と継続記録はRECENT_RUN.mdを参照。
