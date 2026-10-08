# Codexクラウドへの引継ぎ

有限AS分解から全次数Extと小さい直和の交換、総空間比較、Ext交換同型の全成分左作用への適合性を証明しました。
左右の総空間関手の忠実性とexactnessに加え、任意の有限個の元が恒等成分作用の有限和で固定されることを証明済みです。
ASRegularから次数3集中と正次数作用の消滅を導きました。新しいAS仮定はありません。
次は有限台非単位的総代数・総加群構造、成分逆関手とGr(A)圏同値・Ext保存です。
有限長双対性・周期性・定理3.2と系5.2は未証明。両主結果の形式的な文も未実装です。
最新ローカル検証 20261008T062041Z-c4ef97ab：60数学モジュール・636異なる宣言・274 theorem、全段階終了0。
単位1〜8の差分・実測時刻・次の義務はRECENT_RUN.mdとruns/ext-sums-20261008.md。

## 場所・固定環境・権限

- リポジトリ：https://github.com/uedakazushi/as-ginzburg-lean 。作業場所：`/workspace/as-ginzburg-lean`。
- mainへ直接保存。最新ユーザー指示は自律的な継続・検証済み単位の直接push。新規PRなし、force pushなし。
- 今回の開始main：9356dc08b65fd8265659871b8efefb342d12cbcb。各単位の保存SHAはRECENT_RUN.md参照。
- Lean：leanprover/lean4:v4.24.0。mathlib：f897ebcf72cd16f89ab4577d0c826cd14afaafc7。manifest全依存固定。
- 既存の加法的・k線形反変presheafのRightModule定義を保持。
- ASRegularは原論文の有限最小分解の存在(i)と実際の総Ext rank条件(ii)。周期性・WindowSystem・必要なExt同型を追加しない。
- 基盤補題が一般の体で成立しても、主定理の代数閉・標数0の仮定を弱めたとは扱わない。

## 既存の成果と今回の8単位

開始時の51数学モジュールは無変更。右Abelian圏・成分exactness、Yoneda・射影性・EnoughProjectives、
radicalと単純商、minimality、有限ASResolutionとmathlib ProjectiveResolution、実際の線形Abelian.Ext、
syzygyと次数シフト、全次数有限性・高次消滅、数値的AS双対性の両方向まで完成済み。
左Abelian圏・左単純商・左射影基盤、Ext成分左加群の次数集中と左単純商への同型、
左右A-dualとrepresentableの二重双対の対象同型も完成済み。
一般のcanonicalな評価・自然性・有限生成射影への拡張は未証明。
以前の接続記録はdocs/rightmodule_homological_bridge.md、docs/as_resolution_ext_bridge.md、docs/as_finiteness_left_duality.md。

今回9モジュール・8検証単位を追加：

1. finite coproductのHomの自然な有限積表示と余極限交換。
2. 実際Extの接続写像・次元シフトの自然性と関手圏の余核表示。
3. exactな余極限と核・余核の交換、小さい直和のexactness、Homの自然な核表示。
4. 有限AS分解だけから全次数Ext(s_w,-,n)とexactな余極限・小さい直和の交換。包含射への適合性。
5. Ext(s_w,⊕P_i,n)と成分Ext左加群の有限台総空間の比較。ASから次数3集中・kとの線形同型。
6. 左右総空間関手の忠実性・短完全列保存・exactness反映、具体的direct sumとの同型。
7. ⊕P_i上の実際の行列作用、積・局所単位、Ext交換同型の全成分左作用への適合性。ASからExt³上の正次数作用が零。
8. 左右総空間の有限局所単位。成分射影の冪等性と、任意の有限個の元が恒等成分作用の有限和で固定されること。

原論文(1.6)–(1.12)との対応・仮定・利用先はdocs/ext_coproduct_exchange.md。
任意のAや特定のJacobian代数に対しAS分解の存在を証明したとは扱わない。
成分作用の比較や忠実exactな総空間関手だけを、原論文Gr(A)圏同値・Ext保存の代わりにはしない。

## 現在の検査と保存

最新ローカル検証 `20261008T062041Z-c4ef97ab`、全段階終了0、320.816787115秒。
JST 2026-10-08T15:20:41.062310+09:00 → 2026-10-08T15:26:01.879105+09:00。
UTC 2026-10-08T06:20:41.062310+00:00 → 2026-10-08T06:26:01.879105+00:00。
11回帰テスト、ソース監査、固定環境、lake build、全宣言の#print axioms、照合が成功。
60数学モジュール・636異なる明示的宣言・全274 theorem・112 named instanceを監査。
sorry/admit/独自axiomなし。許容依存はpropext、Classical.choice、Quot.soundのみ。
sorryAx、Lean.ofReduceBool、Lean.trustCompilerへの依存なし。
新規数学モジュールに未解決のコンパイルエラー・lint警告なし。初期PathAlgebraの既存lint警告は残る。
161は初期成果の記録であり、宣言数の固定条件ではない。

各単位の差分はruns/ext-sums-20261008-unit*.patch、各新規検証はverification/runs/に保存。
初期14数学モジュール・開始時51モジュールのSHA一致、入力PDFと過去の487ファイル無変更の証拠はverification/ext_sums_preservation.json。
ASGinzburg.leanは9モジュールのimport追加、AxiomAudit.leanは全新規宣言を監査する生成更新。
過去の回収・checkpoints・実行ログを保持する。

接続済みGitHub APIで、ローカル検証済みtreeのSHAとexpected_shaを照合し、force=falseの通常fast-forwardでmainへ保存。
ローカルmainも同じAPI commit objectに同期。過去のCLI push認証エラーが修復されたという主張はしない。
今回の正確なheadのActions・artifact確認はRECENT_RUN.mdの終了記録に追記する。
以前のCI証拠はverification/radical_resolution_github_ci_evidence.jsonとverification/as_finiteness_github_ci_evidence.jsonに保持。

```bash
USE_FRO_CACHE=1 AS_GINZBURG_LEAN_ROOT=/workspace/.cloud-setup/lean-4.24.0-linux \
  bash scripts/check.sh --prepare-cache
```

依存キャッシュがあれば--prepare-cacheを省略。lake updateは不要。
CIはpush/pull_requestごとに固定環境で新規検証し、最新ログをartifactへ保存する。旧成功記録は成功判定に使わない。

## 次に必要な証明義務

1. `⊕_(i,j) A.Hom i j`の有限台非単位的総代数、局所単位、左右の総加群構造を束ねる。恒等成分作用の有限和による有限個の元の固定性は証明済み。
2. 成分を取る逆関手、単位・余単位を持つ原論文Gr(A)との圏同値、実際のExt保存を証明する。
3. canonicalな二重A-dualの評価と自然性、有限生成射影・perfect complex・有限長双対性。
4. D Ext³から区間制限・projective cover・区間同型のcoherenceを構成し、AS条件から周期性を導く。
5. Jacobian商・Ginzburg dg代数・d²=0・外部一般定理・主定理の同型類対応。

一般の全M,N・全次数の自然なHom複体–Abelian.Ext比較も未証明。直和交換には長完全列の自然性を使用した。
古いleftDerived型ProjectiveResolution.isoExtを新しいAbelian.Extの比較と取り違えない。
命題1.4は区間同型を仮定した貼り合わせのみ、命題5.1も未証明。
定理3.2と系5.2は未証明で、形式的定理文も未実装。
実測開始・終了・タスク所要時間と検証所要時間はRECENT_RUN.mdを参照。未測定の過去時間は不明。
