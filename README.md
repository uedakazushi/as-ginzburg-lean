# AS–Ginzburg対応のLean形式化：Codexクラウドでの継続

左右の総加群関手の充満性を証明しました。単位化上の加群射から各成分のk線形写像と自然変換を回収し、総空間で元の射を復元できます。
左右の関手は充満忠実です。既存RightModuleと原論文の仮定を保持し、代数は実際の有限台成分とその総作用を使っています。
次は任意の局所単位付き対象の成分射影像と直接和分解、逆関手、Gr(A)圏同値と実際のExt保存です。essential surjectivityは未証明です。
有限長双対性・周期性・主定理3.2と系5.2は未証明。両主結果の形式的な文も未実装です。
最新ローカル検証 20261008T081457Z-890d1808：69数学モジュール・738異なる宣言・322 theorem、全段階終了0。
単位1〜7の差分・実測時刻・次の義務はRECENT_RUN.mdとruns/total-algebra-20261008.md。

**主定理全体は未完成です。定理3.2と系5.2の形式的な文も、まだ実装していません。**

既存の線形RightModuleを保ち、有限AS分解だけから全次数のExt(s_w,P_i)の有限性と次数4以上の消滅を証明しました。
有限AS分解の存在の下で、元のASRegularと式(1.11)の数値条件の両方向の同値が証明済みです。
具体的な左加群・A-dual・左単純商を構成し、実際のExt(s_w,P_i,p)の成分左加群が
p≠3で零、p=3でs^left_(tau^{-1}w)に同型であることを左作用ごと証明しました。
Hom(P_i,-)・Ext⁰(P_i,-)の余極限交換、左側の射影性・EnoughProjectives・実際のExtの存在も完成しました。
左A-dualも構成し、左右のrepresentableが二重A-dualで元に戻る同型を証明しました。
既存モデルのExt(s_w,⊕P_i)への直和交換は完成。原論文のGr(A)比較、周期性と主定理は未証明です。
69数学モジュール、738異なる明示的宣言、322 theorem、123 named instanceを監査します。初期161宣言も含みます。
現在の実行結果は`verification/results.json`と`RECENT_RUN.md`を参照してください。
数学的な証明に使う定義・仮定は各宣言の型に明記してあります。
独自公理、`sorry`、`admit`を使って主定理を完成扱いにすることはしていません。

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

生成条件・WindowSystem・幾何的な共役の入力を原論文から導く部分は未証明です。数値Ext表はASRegularから接続済みです。
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

最新ローカル検証 `20261008T081457Z-890d1808`、全段階終了0、359.500822585秒。
UTC 2026-10-08T08:14:57.146631+00:00 → 2026-10-08T08:20:56.647458+00:00。
JST 2026-10-08T17:14:57.146631+09:00 → 2026-10-08T17:20:56.647458+09:00。
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
