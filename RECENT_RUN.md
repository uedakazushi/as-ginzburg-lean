# 有限AS分解のHom・高次Extと直和の交換

目的：既存RightModuleと実際のAbelian.Extを保ち、原論文(1.6)の有限分解から、
Homと直和の自然な交換、高次Extの直和交換を証明する。
周期性・必要なExt同型・主定理相当の結論を新しい仮定に加えない。
Gr(A)比較、定理3.2・系5.2の形式的な定理文と証明は未実装。

実測開始：2026-10-08 14:02:20 JST / 05:02:20 UTC（秒精度clock観測）。
開始main：9356dc08b65fd8265659871b8efefb342d12cbcb。
このコミットのActions 37728666933はsuccess。
AGENTS/HANDOFF/STATUS/GAPS・現行と回収results・RECENT_RUN・最新runを確認し、
docs/source.pdfの§1.2–1.3、(1.4)–(1.12)と既存Lean定義を照合した。

現在：有限coproductのHomと余極限の自然同型を実装中。
最初のAPI調査では未取得のmathlib FunctorCategory.oleanにより終了1。
固定mathlibの公式キャッシュを追加取得する。バージョン・manifestは変更しない。
数学的な証明単位の成功検査はまだない。

保存先は直接main、通常のfast-forward、force=false、新規PRなし。
旧版・入力PDF・recovery/checkpointsは保持する。
終了時刻と経過時間は終了記録時に実測する。

## 単位1：有限coproductのHomと余極限の自然な交換

実際のcoproductへの制限写像からHom–有限積の成分同型とその射に関する自然性を証明した。
有限biproductのcolimIsoLimにより有限積関手も余極限を保存し、各因子のHomが保存するshapeの保存が有限coproductへ閉じる。
representableの有限coproduct、AS分解の第1・第2項、実際のExt⁰に適用した。
交換はcanonicalなpreservesColimitIsoであり、Hom交換同型を新しい仮定にしていない。
対象universeが許す余極限shapeを明示し、原論文の矢添字はType 0の有限型のまま。
利用先：有限AS分解へのHomと直和の交換、高次Ext(s_w,⊕P_i)の比較。
次：実際のExtの接続写像・次元シフトの自然性、短完全列からのHomのkernel表示とExt¹のcokernel表示。
高次Ext・直和の交換、Gr(A)比較、原論文(1.12)全体はまだ未証明。

個別API調査の未取得oleanと型・自然性の草稿エラーは修正済み。
固定mathlibの公式キャッシュを追加取得した。最終個別Lean終了0、新規全体検査終了0。

検証：`20261008T050918Z-e404c546`、232.167668385秒、全段階終了0。
JST 2026-10-08T14:09:18.501217+09:00 → 2026-10-08T14:13:10.668891+09:00。
UTC 2026-10-08T05:09:18.501217+00:00 → 2026-10-08T05:13:10.668891+00:00。
52数学モジュール・517異なる宣言・224 theorem。
差分：runs/ext-sums-20261008-unit1.patch。全theoremを監査し、許容公理3種類のみ。

単位1のmain保存：8d1253c9bcf45b93931bcade1182db565035a92e。ローカル検証済みtreeをSHA照合し、APIで通常のfast-forward保存。

### 単位2：実際のExtの自然な接続写像・次元シフト・余核表示

`RightModuleExtNaturalSequence.lean`で、第一引数の前合成・長完全列の接続写像・
射影的な中項に沿う次元シフトを、第二引数に関する自然変換・自然同型として実装。
長完全列の成分ごとのexactnessと接続写像の全射性から関手圏の余核の普遍性を証明し、
`Ext(X₃,-,n+1)`を`Ext(X₂,-,n) → Ext(X₁,-,n)`の実際の余核として自然に表示した。
余核射と実際の接続写像との一致も証明済み。

利用先：有限AS分解の三つの短完全列に適用し、Homの直和交換から高次Extへ移す。
次の義務：核・余核を取る関手の交換の閉性、syzygyのHom交換、全次数Extの直和交換。
Homの消滅・周期性・必要なExt同型を新しい仮定として追加していない。
定理3.2・系5.2の証明および形式的定理文、Gr(A)比較は未完成。
個別Lean検査：natural-sequence-draft8.log、終了0、警告なし。

検証：`20261008T052305Z-ec668cf7`、246.312751335秒、全段階終了0。
JST 2026-10-08T14:23:05.417104+09:00 → 2026-10-08T14:27:11.729861+09:00。
UTC 2026-10-08T05:23:05.417104+00:00 → 2026-10-08T05:27:11.729861+00:00。
53数学モジュール・529異なる宣言・227 theorem。
差分：runs/ext-sums-20261008-unit2.patch。全theoremを監査し、許容公理3種類のみ。
