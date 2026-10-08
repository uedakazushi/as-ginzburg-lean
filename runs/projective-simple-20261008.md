# 射影性・単純加群の自律的継続記録

開始観測：2026-10-08 10:43:23 JST（2026-10-08T01:43:23+00:00、秒精度）。
目的：既存RightModuleの表現可能対象の射影性、radical・単純加群と分解の基盤を具体的に形式化する。
ユーザーの最新指示により、新規PRを作らず、成功した証明単位をmainへ直接commit・pushする。
以前のmainへマージしない制約と目標ごとの再開確認は、この指示で更新された。
原論文の仮定を弱めず、周期性・必要なExt同型・主結果を追加仮定にしない。

## 初期同期と前回成果の統合

リモートmainの開始HEAD：`0d806291edbaf56b4ff30b77e45d2a632a207a27`。
前回の検証済み`codex/rightmodule-abelian-20261008`（`4547b79`）をmainへ通常のmergeで統合。
mergeコミット：`5780346065afc07322c243b2953877a691769ae0`。
force push・履歴の書換えなし。初期の原論文照合は§1.2 (1.5)–(1.7)、既存定義を再確認。
最新の統合後検証：`20261008T014511Z-189d79de`、終了0、19.964866秒。
全202宣言の監査・ビルド・11回帰テスト・固定環境・照合が終了0。
次：全右加群に対する線形Yoneda評価同型を構成し、成分の全射性からrepresentableのProjectiveを導く。
終了時刻・経過時間は最後の記録で実測して追記する。

## 単位1：線形Yonedaとrepresentableの射影性

`representableYonedaEquiv i M : (P_i ⟶ M) ≃ₗ[k] M_i`と逆写像の右作用の公式を完成。
自然性を証明し、epiの各成分の全射性から`representableProjective`を構成。
任意の右加群Mに対する実際のHom同型であり、AS条件やExt同型を仮定していない。
検証：`20261008T014813Z-d160e1b1`、42.293801秒、全段階終了0。
開始UTC 2026-10-08T01:48:13.771735+00:00、終了UTC 2026-10-08T01:48:56.065545+00:00。
208異なる宣言・99 theorem・11回帰テスト・lake build・公理監査・固定環境・照合が成功。
初期の一時ファイルでのYoneda自然性の型合わせとidentity rewriteを修正し、解消。
差分：runs/projective-simple-20261008-unit1.patch。
次の利用先：representableの直和から任意のMへのepiを構成してEnoughProjectivesを証明する。
その後、正次数radicalと単純商、最小分解・実際のExtへ進む。

## 単位2：EnoughProjectives

全頂点・全要素で添字付けたrepresentableの直和から任意のMへのepiを構成。
`rightModuleEnoughProjectives`はmathlibの標準クラスであり、実際の射影提示から証明。
有限生成・最小性・長さ3は主張していない。
検証：`20261008T015423Z-b4287b26`、42.925535秒、全段階終了0。
開始UTC 2026-10-08T01:54:23.096822+00:00、終了UTC 2026-10-08T01:55:06.022365+00:00。
差分：runs/projective-simple-20261008-unit2.patch。
次：右作用で閉じた成分submoduleを束ね、正次数radicalと商s_vを構成する。

## 単位3：右作用で閉じた部分加群と商

成分subspaceと右作用の閉性から実際の線形presheafを構成する`RightSubmodule`を定義。
包含のmono、mathlib cokernelとしての商と射影epi、短完全列を証明。
検証：`20261008T015621Z-6b22140d`、47.605570秒、全段階終了0。
開始UTC 2026-10-08T01:56:21.914268+00:00、終了UTC 2026-10-08T01:57:09.519848+00:00。
226異なる宣言・100 theoremを監査。
差分：runs/projective-simple-20261008-unit3.patch。
次：positive条件からradicalの閉性を証明し、s_vの成分・単純性を確認する。

## 単位4：正次数radicalと本物の単純商s_v

`representableRadical`の右作用による閉性をpositive条件から証明。
その成分が`positiveActionSpan`（正次数の右積のspan）に等しいことも証明。
商`simpleRightModule`は選ばれた実際のcokernel。対角成分は1次元、他はIsZero、
mathlibの`Simple`を証明し、radical→P_v→s_vの短完全列を得た。
検証：`20261008T020014Z-8c881eba`、54.947996秒、全段階終了0。
開始UTC 2026-10-08T02:00:14.316187+00:00、終了UTC 2026-10-08T02:01:09.264189+00:00。
240異なる宣言・106 theoremを監査。
差分：runs/projective-simple-20261008-unit4.patch。
次：標準projective resolutionと実際のExtを供給し、有限最小分解の実装へ接続する。

## 単位5：標準射影分解と実際のExt

`ProjectiveResolution.of`から任意の右加群の標準分解と正次数の完全性を得た。
証明済みEnoughProjectivesから`HasExt`をHomのuniverse vで導出。
実際のderived-category Ext⁰(P_i,M)とM_iの加法的同型、
Extⁿ⁺¹(P_i,M)=0（第1引数が射影対象）を証明。
これはExtⁿ(s_u,P_v)の計算・AS条件ではない。全高次Extのk作用とHom複体比較は残る。
検証：`20261008T020142Z-06538c59`、61.239278秒、全段階終了0。
開始UTC 2026-10-08T02:01:42.423333+00:00、終了UTC 2026-10-08T02:02:43.662622+00:00。
245異なる宣言・108 theorem・37 named instanceを監査。
差分：runs/projective-simple-20261008-unit5.patch。
次：一般の正次数radical、微分の像がradicalに入るminimality、(1.6)の有限四項分解、
全Extのk線形性・実際のHom複体比較・(1.7)の次元条件。

## 検査と保存の一覧

| 単位 | 新規run | 宣言 / theorem | 実測検証秒 | 終了コード | mainコミット |
|---|---|---:|---:|---|---|
| 統合後 | `20261008T014511Z-189d79de` | 202 / 96 | 19.964866 | 全段階0 | `4e31f63` |
| 単位1 | `20261008T014813Z-d160e1b1` | 208 / 99 | 42.293801 | 全段階0 | `2e87d63` |
| 単位2 | `20261008T015423Z-b4287b26` | 214 / 99 | 42.925535 | 全段階0 | `22c4b6c` |
| 単位3 | `20261008T015621Z-6b22140d` | 226 / 100 | 47.605570 | 全段階0 | `dc17b2b` |
| 単位4 | `20261008T020014Z-8c881eba` | 240 / 106 | 54.947996 | 全段階0 | `86853a5` |
| 単位5 | `20261008T020142Z-06538c59` | 245 / 108 | 61.239278 | 全段階0 | `2ac9d17` |

検証時間の合計：268.977047秒。タスク全体の時間とは別の値。
各コミットのgit push origin mainは終了0。新規PRを作っていない。
初期14モジュールとPDFのハッシュ一致、checkpoints/・recovery/無変更を再確認（終了0）。
原論文(1.5)のradicalと単純商は既存presheafモデル上で証明。
当初の一時Leanファイルには自然性の型合わせ、Subtypeのext、opの型注釈でコンパイルエラーがあり、すべて修正。
公開した証明単位の全検証は成功。未解決のコンパイルエラーなし。既存lint警告は残る。
README/HANDOFF/STATUS/GAPS、原論文とmathlibの対応記録を更新。
過去の稼働時間は不明で、推測して実測時間にしていない。

## mainの数学的コミットのCI

コミット`2ac9d17cf715af3bb44326142e5b2ec994305dc2`のActionsはsuccess。
https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37715985785
CI内の新規検証`20261008T020400Z-88ab813a`は終了0、201.451202秒。
開始UTC 2026-10-08T02:04:00.186431+00:00、終了UTC 2026-10-08T02:07:21.637638+00:00。
setupは終了0、23.357808701秒（正確な開始・終了はraw job logに保存）。
キャッシュ取得を含む全7段階が終了0。245異なる宣言・108 theorem・37 named instance。
ログartifact `lean-verification-37715985785-1`（ID 11523548364、12ファイル）の保存を確認。
前の4証明単位と初期統合のmain CIもsuccess。
証拠：verification/projective_simple_github_ci_evidence.json、verification/ci-projective-simple-main.log。
この後の最終記録コミットは、同一の数学的ソースで独立のpush CIを起動する。
その結果はGitHub Actionsで確認できる。

## 終了記録

計測開始：2026-10-08T10:43:23+09:00（2026-10-08T01:43:23+00:00）。
計測終了：2026-10-08T11:09:58+09:00（2026-10-08T02:09:58+00:00）。
実測経過：1595秒（26分35秒）。
実測時計のUTC時刻差、秒精度。実装・ローカル検査・数学的CI・引継ぎの記録区間を測定した値で、
最後の記録commit/push前に計測を閉じた。サービスの稼働時間の保証ではない。
検証時間の合計は別掲。過去の時間は不明。

完成：既存RightModule上の線形Yoneda、射影性・十分な射影対象、部分加群と商、
正次数radical・s_vと単純性、標準分解・実際のExtへの接続。
未証明：一般radicalの閉性・minimality、(1.6)の有限四項分解、全Extのk線形性、Hom複体比較、
(1.7)のExt(s_u,P_v)条件、presheaf↔Gr(A)の明示的同値、AS条件からの周期性と主結果。
定理3.2・系5.2は未証明で、形式的な定理文も未実装。
未解決のコンパイルエラーなし。git diff --checkと記録リンク・現在のLean SHA-256照合も終了0。
README/HANDOFF/STATUS/GAPS/AGENTSと原論文の対応記録を更新した。
新規PRなし。検証済み前回ブランチの統合と証明単位の直接main pushを実施。
