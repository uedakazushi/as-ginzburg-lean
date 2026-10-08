# 現在の状況

2026年10月8日。既存RightModuleの定義を保ち、Abelian構造・ホモロジー接続に加えて、
射影対象、十分な射影対象、正次数radical、単純商、標準射影分解と実際のExtへの接続を完成。
今回追加した5数学モジュールは、各証明単位で検査して直接mainへcommit・pushしました。
初期14モジュールと入力PDFは旧SHA-256一致、checkpoints/・recovery/は無変更。

| 項目 | 現在の結論 |
|---|---|
| lake build | 成功、終了0、3321 jobs |
| 個別公理監査 | 245異なる名前、終了0。全明示的宣言・37 named instanceを含む |
| 補助定理 | 108 theorem。全件が監査対象 |
| sorry / admit / 独自axiom | ソース内0件 |
| 許容公理 | propext、Classical.choice、Quot.soundだけ |
| 禁止依存 | sorryAx、Lean.ofReduceBool、Lean.trustCompilerはなし |
| 主結果 | 定理3.2・系5.2は未証明、形式的な文も未実装 |
| 保存方針 | ユーザーの最新指示により直接mainへpush。新規PRなし |

最新ローカル検証 `20261008T020142Z-06538c59`：全段階終了0、61.239278秒。
UTC 2026-10-08T02:01:42.423333+00:00 → 2026-10-08T02:02:43.662622+00:00。
11回帰テスト、ソース監査、固定環境、lake build、全宣言の#print axioms、照合が成功。

## 形式化状況

| 論文中の位置 | Leanファイル | 実装・証明済み | 残る範囲 |
|---|---|---|---|
| §1.1、(1.1) | `CutQuiver.lean` | cut箙、被覆頂点、heightの全単射、正のwinding、pathの次数公式 | 被覆道代数をZ-代数として束ねる同定 |
| §1.1の巡回空間 | `CutPotential.lean` | 回転商の自由ベクトル空間、cut次数、唯一のcutの分割とnormal form | 閉じた可合成道の部分空間とkQ/[kQ,kQ]の同定 |
| (3.8) | `CyclicDerivative.lean` | 巡回微分の実装、回転不変性、cut復元恒等式 | Jacobianイデアルおよび商代数との接続 |
| 道代数 | `PathAlgebra.lean` | 成分の自由ベクトル空間、双線形積、単位元、結合則 | 関係イデアルとその商、unrolling |
| (1.4) | `ZAlgebra.lean` | 具体的な成分、双線形な積、局所単位元、connected・positive・finite条件 | 原論文のAS正則性の定義 |
| 命題1.2の帰納法 | `ZAlgebra.lean` | 成分が生成元と短い積に分解されれば全成分を生成する | 分解条件を最小射影分解から導くこと、核が矢イデアルの二乗に入ること |
| (1.5) | `Representables.lean` | k線形圏と右線形presheaf、YonedaのHom同型、逆向きHomの消滅、自己Homの次元1 | 直和・局所単位元付き加群との明示的同値 |
| §1.2の加群圏・(1.6)の基盤 | `RightModuleAbelian.lean`、`RightModuleHomology.lean` | (余)極限の閉性、Abelian構造、核・余核・homologyの成分同型、exactness・短完全列・mono/epiの成分判定 | 実際の射影分解・minimality・Extとの比較 |
| (1.5)の射影対象 | `RightModuleProjectives.lean`、`RightModuleEnoughProjectives.lean` | 全Mへの線形Yoneda同型、P_vの射影性、representableの直和による射影提示、EnoughProjectives | 有限生成のprojective coverと最小分解 |
| (1.5)の単純商 | `RightSubmodules.lean`、`SimpleRightModules.lean` | 右作用で閉じた部分加群、商の短完全列、P_v A_{>0}との成分同定、s_vの対角1次元・他の成分零とSimple | 一般Mの正次数radicalの閉性、minimality |
| (1.6)–(1.7)の基盤 | `RightModuleExt.lean` | 標準projective resolutionと正次数exactness、実際のderived-category Ext、Ext⁰(P_i,M)≃+M_i、高次Ext(P_i,M)=0 | 四項有限最小分解、全Extのk線形性、Hom複体による計算、Ext(s_u,P_v)の次元条件 |
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


初期161宣言を含む全245監査対象を`verification/declarations.json`に列挙。
161は歴史的な件数であり、将来の追加を妨げる固定条件ではありません。
`InWindow.mono`の完全名と監査一覧・コマンド・ログの重複／漏れを検査します。

今回の5単位は、既存の体・ZAlgebraの条件から証明しました。
周期性、必要なExt同型、AS条件と同等の結論を仮定に追加していません。
一般の体で成立する補題であり、原論文の主定理の代数閉・標数0の仮定を弱めていません。
`Simple`、`EnoughProjectives`、`HasExt`はmathlibの標準定義を実際の構成から証明したものです。

## 残る範囲と検査記録

- `s_v`は既存の線形presheafモデルで構成済み。局所単位元付き直和加群`Gr(A)`との明示的同値は未実装。
- 標準projective resolutionは一般に無限で、有限性・最小性・長さ3を証明していません。
- Ext⁰の接続は加法的同型。全高次Extのk作用・線形性とHom複体による計算は未実装。
- Extⁿ(P_i,M)=0は第1引数が射影対象の場合。論文(1.7)のExtⁿ(s_u,P_v)を計算した結果ではありません。
- AS正則性・Ginzburg正則性の本体と主定理文は未実装。
- 以前の次元表・WindowSystem・共役などの条件付き補題では、原論文から入力を導く部分が未証明。
- 新規数学ファイルに未解決のコンパイルエラー・lint警告はありません。既存のlint警告は残存。
- 原ファイルの保存確認は`verification/projective_simple_preservation.json`。
- 証明単位ごとの差分・実測時刻・終了コード・次の義務は`runs/projective-simple-20261008.md`と各unit patch。
- 最新のActions・リモート保存・タスク全体の実測時間は`RECENT_RUN.md`参照。

ユーザーは形式化の自律的継続を明示的に指示しています。通常の次の補題のために再開確認は不要です。

数学的コミット`2ac9d17`のmain Actionsはsuccess、12ファイルの最新artifact保存を確認。
証拠は`verification/projective_simple_github_ci_evidence.json`とRECENT_RUN.md。
