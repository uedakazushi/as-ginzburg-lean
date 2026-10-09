# AS–Ginzburg対応のLean形式化：Codexクラウドでの継続

## 現行の最小関係・foundation・ポテンシャル候補（単位186〜213）

単位132〜185で、本来のGinzburgRegular⇒元のASRegular全体、foundationへのexact制限と原論文(3.5)の実際のProjectiveResolution/単純射影次元≤2/高次Ext消滅、最小関係の本来の定義と基底持上げを全体検証済み。

単位186〜213で、真のIJと最後の矢cover核、実際I/IJと本来のcategorical AS核の同型/代表元/元の作用自然性、真のJIの像と核のpositiveActionSpanの一致を証明。IJ+JI分母を同定し、真のI/(IJ+JI)と核のradical商の全成分線形同型、第零sheetのreverse cut矢添字の基底とfinrank、本来ASRegularだけから実際の関係代表元とmod IJ+JI生成性まで全体検証済み。

WORK214〜242は個別Lean実終了0・診断なし、今回の全体監査には未収録。元のASRegularから最小関係を非cut道へ降下しcut=0/長さ≥2支持を証明。原論文のΦB=Σ[ρrρ]を既存の実際の閉路Potential型で構成し、全cut微分が選んだrρ、unroll後に元の表示核とI/(IJ+JI)の基底商類へ戻ることを証明。有限高さ差帰納法により第零sheetの全表示核が選んだ最小関係の本来の両側イデアルで生成されることも証明。単位225の一般補題の条件は単位227で元のASRegularから導出済み。有限FoundationAlgebra反対環ModuleCatへの加法的忠実な実際の総空間関手と、実際の成分冪等射影像から既存FoundationRightModuleへの逆関手を構成。成分埋込/単位和/直交性、総加群射影の元成分との一致、kスカラー制限との線形比較を個別検証済み。

未証明：両方向合成の自然同型と有限foundation環ModuleCatとの圏同値、現行FoundationAlgebraのA.{u,u}からu,vへの宇宙一般化、非cut自由道商とfoundation環の同型、周期整合したfinitecut基底降下、候補ΦBのGinzburgRegularと元の代数回収、Reyes/Hanihara/Keller接続、選択独立性/同型類対応/§5quadratic。候補の構成や生成性を正則性/主定理完成と扱わない。定理3.2と系5.2は未証明・正式Lean定理文未実装。周期性/必要Ext表/Calabi–Yau性/主結論を新しい仮定にしない。

最新全体成功run20261009T073318Z-9f470afd：630数学モジュール、3722異なる宣言、2013 theorem、全6段階/終了0、現在の公開ソースSHA一致、許容公理propext/Classical.choice/Quot.soundのみ。重複/監査漏れ/holes/独自axiom/禁止依存なし。UTC07:33:18.809605→08:17:02.992333、実測2624.182717499秒。wrapperも実終了0、2624.236277774秒。

前main80eee11のGitHub CI run37894259808は全7検査0/success、全文ログ/artifact証拠を回収済み。現main5c6e119のCI run37899618525は最後の取得時点でin_progress。旧headの成功を現行の成功と扱わない。最新630公開ソースを通常fast-forwardでmainへ保存し、そのheadのCIを確認する。

過去の単位説明は当時の状態として読み、現在の判定にはこの概要と現行SHAに対応した終了コードを使う。


## 確認済みの代表的な内容

- cut付き有限箙と被覆の頂点、heightの全単射、winding degreeの正値性。
- 道の線形化、双線形な積、局所単位元、結合則。
- 実際の局所有限な正に有向なZ-代数と、そのk線形圏・右表現可能加群。
- 線形Yonedaによる表現可能加群のHomの同定と、逆方向のHomの消滅。
- 既存`RightModule`の(余)極限の閉性、核・余核・有限積とAbelian圏構造。
- 頂点評価による核・余核・mathlibのhomologyの同型、exactnessの像＝核による成分判定、
  短完全列・単射・全射の成分判定。原論文との対応は[接続記録](docs/rightmodule_homological_bridge.md)。
- 任意のMへの線形Yoneda同型、表現可能加群の射影性と直和による射影提示。
- 正次数の右積のspanとradicalの一致、s_vの対角成分1次元・他の成分零、単純性と短完全列。
- 標準射影分解、実際のExtの存在とk線形性、Ext⁰の線形Yoneda同型と高次Ext(P_i,M)の消滅。
- 一般radical・minimality、有限AS分解からmathlib ProjectiveResolutionへの変換、実際のsyzygy短完全列。
- 具体的ASRegular、実際のExt³(s_(tau v),P_v)≃k、他Ext消滅、数値的AS双対性の順方向と有限台の表。その後、有限性を導いて逆方向も証明済み。
  [原論文・実装・残る証明義務](docs/as_resolution_ext_bridge.md)。
- 有限AS分解からの高次Ext消滅・全次数有限性と数値的同値、具体的左加群・左単純商・Extの左作用、
  Hom/Ext⁰の余極限交換と左側の射影性・EnoughProjectives・Extの存在。
  [前回の左双対接続記録](docs/as_finiteness_left_duality.md)。
- 全次数Extと小さい直和の交換、左右の総空間関手の忠実性とexactness、直和上の行列作用と成分左作用への適合性、左右総空間の有限局所単位による同時固定。
  [今回8単位の接続記録・残る義務](docs/ext_coproduct_exchange.md)。
- 巡回微分の回転不変性と、cut次数1での
  \(\Phi=\sum_{\rho\in C}[\rho\partial_\rho\Phi]\)。
- 正の次数を下げるHilbert漸化式の一意性、およびquadratic型の数値解
  \(h_m=\binom{m+2}{2}\)と二次式による増大上界。
- 本物のテンソル積による(3,3,3)係数表示、cut関係への線形同型、27次元性。
- 三角形箙のcut次数1の閉路が長さ3を持つこと。

次の結果は**条件付きの中間補題**です。

- 正次数成分の分解が与えられた場合の生成の帰納法。
- 任意の有限台次元表についての数値補題。今回、実際のExtから有限台表と非零項を導く順方向も接続済み。
- coherentな有限区間同型が与えられた場合の大域的な周期同型の構成。
- 完全忠実な線形関手と対象同型が与えられた場合の、Homの積を保つ共役。

最小分解d₁からの生成条件・原論文(1.8)/(1.10)・実際の道代数全射は証明済みです。構成した生成元についての核の矢イデアル平方への包含(1.9)と道代数商同型も証明済みです。任意の基底の持上げ・選択の独立性、最小関係と幾何的な共役・tilting・CY completionへの接続は未証明です。数値Ext表とcoherentなWindowSystemおよび正負周期性はASRegularから証明済みです。
詳細は[STATUS.md](STATUS.md)、[GAPS.md](GAPS.md)、[HANDOFF.md](HANDOFF.md)を参照して下さい。

## 再現

Lean `leanprover/lean4:v4.24.0`、mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`を使います。
`lakefile.lean`はタグでなくコミットを指定し、`lake-manifest.json`は全依存コミットを固定します。
Python 3、Git、bash、およびelanか固定Leanの配布物が必要です。

```bash
elan toolchain install leanprover/lean4:v4.24.0
bash scripts/check.sh --prepare-cache
```

キャッシュが揃った後は`bash scripts/check.sh`で検証できます。
`--prepare-cache`は実際にimportするmathlibモジュールとその依存のキャッシュを取得します。
キャッシュ取得自体は本プロジェクトの証明の検証ではありません。
再現のために`lake update`を実行する必要はありません。

今回のCodexクラウド環境では、用意済みの固定配布物を次のように使えます。

```bash
USE_FRO_CACHE=1 AS_GINZBURG_LEAN_ROOT=/workspace/.cloud-setup/lean-4.24.0-linux \
  bash scripts/check.sh --prepare-cache
```

`USE_FRO_CACHE=1`はmathlib公式キャッシュクライアントのCloudflare取得先を選びます。
今回のクラウドではAzure取得先にCONNECT 403があり、許可済みのCloudflare取得先を使用しました。
コマンド実行環境のネットワーク権限と既存プロキシが必要です。
キャッシュは既定で`.lake/cache/mathlib/`に保存し、`MATHLIB_CACHE_DIR`で変更できます。
古い特殊環境向けの`AS_GINZBURG_PROC_SELF_FIX=1`は通常不要で、今回の検証でも使いません。

`check.sh`と`with_lean.sh`にはGitで実行権限を記録し、内部のラッパー呼出しも`bash`経由にしました。
`ASGinzburg.lean`は全数学モジュールをimportします。
`AxiomAudit.lean`は生成された全明示的宣言と名前付きinstanceに`#print axioms`を実行します。
自動生成の構成子・射影等はこの明示的宣言件数に含みません。
許容する依存公理は`propext`、`Classical.choice`、`Quot.sound`のみです。
`sorry`、`admit`、独自`axiom`、`sorryAx`、`Lean.ofReduceBool`、`Lean.trustCompiler`を拒否します。
監査一覧・コマンド・ログを重複検査し、現在のソースと一対一で照合します。
161は初期成果の件数であり、将来の宣言追加を制限する固定条件ではありません。

## CIと検証記録

GitHub Actionsの`.github/workflows/lean.yml`はpushとpull_requestで同じ検証コマンドを実行します。
プロセスの終了コードをそのまま失敗に反映し、成功・失敗のどちらでも今回のログをartifactに保存します。
履歴の成功ログをCIの成功判定に使いません。

- `verification/runs/<run-id>/`：毎回新規作成するログ、宣言一覧、環境と検証結果。
- `run.json`：各コマンド・終了コード・UTC開始／終了時刻・単調時計の実測秒・ログSHA-256。
- `verification/latest.json`：最新試行への参照。失敗時も更新。
- `verification/{build.log,axioms.log,declarations.json,results.json}`：最新試行の写し。
- `checkpoints/20261007/verification/`：旧検証記録の無変更保存。旧監査は161コマンド／160異なる名前で、`InWindow.mono`が欠落していました。
- `checkpoints/20261007/{AxiomAudit.lean,preservation.json,recovered_docs/}`：旧監査ソース・保存確認・改訂前の文書。
- `recovery/`と`docs/source.pdf`：過去の回収記録と入力論文。無変更。
- `RECENT_RUN.md`と`runs/`：タスクの目的・差分・実測時間・検査・残ったエラー。
- `AGENTS.md`：継続作業の規約。最新の指示により、自律的に形式化を継続して検証済み単位を直接mainへpushします。

**ビルド成功は実装済み補題の検証を意味します。主定理の完成を意味しません。**

最新ローカル検証 `20261009T063603Z-82270355`、全段階終了0、2515.621690114秒。
UTC 2026-10-09T06:36:03.452819+00:00 → 2026-10-09T07:17:59.074513+00:00。
JST 2026-10-09T15:36:03.452819+09:00 → 2026-10-09T16:17:59.074513+09:00。
11回帰テスト、ソース監査、固定環境、lake build、全宣言の#print axioms、照合が成功。

証明単位ごとのmainへの保存・Actions・実測時間はRECENT_RUN.md参照。
CLI push認証エラー後は接続済みGitHub APIで検証済みtreeを通常のfast-forward保存。
新規PRなし。数学的ソースの保存確認はverification/ext_sums_preservation.json。

以前のradical-resolutionタスクの最終数学コミットc314180の[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37722129359)はsuccess。
369宣言・177 theoremの監査と12ファイルの当該実行artifact保存を確認。
実行ログと実測時刻はverification/radical_resolution_github_ci.logおよびCI evidence JSONに保存。

前回as-finitenessタスクの最終数学コミット2863bbaの[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37727782672)はsuccess。
505宣言・全223 theoremの新規監査、12ファイルの当該実行artifact保存を確認。
CI検証はUTC 2026-10-08T04:30:31.595999+00:00 → 2026-10-08T04:38:32.459227+00:00、
単調時計で480.863225234秒、終了0。
証拠はverification/as_finiteness_github_ci_evidence.jsonと同名のCI log。
この以前のタスクの終了保存は文書・記録のみ。今回の数学追加の成功判定には、新しい検証と正確なheadのCIを使用する。

前回ext-sumsの数学コミット6666e09の[main CI](https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37737755500)はsuccess。
636異なる宣言・全274 theoremの新規監査、全7段階終了0、12ファイルのartifact 11532667814保存を確認。
CI検証UTC 2026-10-08T06:28:37.911543+00:00 → 2026-10-08T06:36:04.010329+00:00、単調時計446.098779473秒、終了0。
証拠はverification/ext_sums_github_ci_evidence.jsonと同名のCI log。
この確認後の終了記録の保存は文書・ログのみ。同じ数学ソースを保持し、そのpushも新規CIを開始する。
