# RightModule Abelian構造の実装記録

目的：既存の線形右加群の定義を保ち、Abelian圏構造とmathlibのホモロジー代数に接続する。
タスク開始：2026-10-08T00:20:15+00:00（UTC時計の観測、秒精度）。
作業ブランチ：`codex/rightmodule-abelian-20261008`。mainへマージしない。
作業中。終了時刻と全所要時間は終了前に追記する。

## 単位1：極限・余極限の閉性

- 完成：`rightModuleProperty_closedUnderLimits`、`rightModuleProperty_closedUnderColimits`。
- 図式の各対象の加法性・k線形性を、射影のjoint monicity／包含射のjoint epicityと自然性から導く。
- 仮定はModuleCatに当該形状の(余)極限が存在することだけ。有限図式ではmathlibが供給する。
- 定義`RightModule`、既存14数学モジュール、PDFは変更していない。ルートimportに新モジュールを追加。
- 原論文§1.2の`A.Hom u v = e_v A e_u`の右作用`M_v → M_u`と反変関手の向きを照合。
  一般Field上の圏論的補題であり、原論文の代数閉・標数0などの主定理の仮定を変更しない。
- 検証：`20261008T002450Z-2b39e40d`、全段階終了0、28.790644秒。
  UTC 2026-10-08T00:24:50.132119+00:00 → 2026-10-08T00:25:18.922773+00:00。
  lake build、公理監査174異なる宣言／86 theorem、回帰テスト10件、固定環境、照合が成功。
- 許容公理：propext、Classical.choice、Quot.soundのみ。禁止placeholder・独自公理・禁止依存なし。
- 途中の失敗：`20261008T002426Z-5860c6e4`のbuild終了1。
  余錐のconst functorの展開を含む自然性のrewriteを修正し、解消。
- 次の利用先：full subcategoryのinclusionが(余)極限をcreateするmathlib定理。
  次の証明義務：核・余核・有限積の存在と保存、coimage-image比較の同型性、exactnessの成分判定。
- `git diff`を`runs/rightmodule-abelian-20261008-unit1.patch`へ保存する。

主定理3.2・系5.2は未証明、形式的な定理文も未実装。AS条件・Ext条件・周期性を追加仮定にしない。

## 単位2：Abelian構造と核・余核の保存

- 完成：任意の存在する形状の(余)極限のfull subcategoryへの持ち上げとcreate、有限積、
  余像→像の比較射の同型性、`rightModuleAbelian`、包含の有限(余)極限保存。
- 単位1のコミット：`2798d6f`、push終了0。
- mathlibの`ModuleCat`とambient関手圏のAbelian構造、full faithful inclusion、
  `PreservesCoimageImageComparison.iso`と`Abelian.ofCoimageImageComparisonIsIso`を使用。
- 長い宣言名でLeanの公理リストが折り返されるため、監査ログ解析を複数行に対応させた。
  重複・禁止公理・切れたリスト・未認識出力を拒否する回帰テストを追加（合計11件）。
- 検証：`20261008T002911Z-45d4d8c7`、全段階終了0、14.815409秒。
  UTC 2026-10-08T00:29:11.909605+00:00 → 2026-10-08T00:29:26.725020+00:00。
  ビルド、183異なる宣言の公理監査（86 theorem）、11回帰テスト、固定環境、照合が成功。
- 途中の失敗：`20261008T002644Z-f4e57128` build終了1（有限余極限保存の明示的introで解消）、
  `20261008T002737Z-ed8c1a7f` report終了1（公理出力の折り返し対応で解消）。
- 差分：`runs/rightmodule-abelian-20261008-unit2.patch`。
- 次の利用先と証明義務：頂点評価がホモロジーを保存すること、核・余核・homologyの成分同型、
  exactnessと線形写像の像＝核の同値、短完全列の成分判定。

## 単位3：成分ホモロジー・exactnessへの接続

- 完成：`rightModuleEvaluation`、評価の加法性・有限(余)極限保存・homology保存。
  核・余核・mathlibのShortComplex.homologyの成分同型と構造射の互換性。
  包含後のexactnessとの同値、成分wise exactness、線形写像の像＝核との同値。
  mono/epiと成分wise mono/epi、injective/surjectiveの同値、ShortExactの成分判定。
- 単位2のコミット：`0c7965a`、push終了0。
- Draft PR #2：https://github.com/uedakazushi/as-ginzburg-lean/pull/2 。
  基盤整備PR #1のブランチをbaseとする後続PR。mainは未変更、未マージ。
- 検証：`20261008T003239Z-336ff83a`、全段階終了0、39.289198秒。
  UTC 2026-10-08T00:32:39.439384+00:00 → 2026-10-08T00:33:18.728587+00:00。
  lake build、公理監査202異なる宣言／96 theorem、11回帰テスト、環境、照合が成功。
- 初期14数学モジュールとPDFの旧SHA-256一致も再確認、終了0。
  新規数学ファイル2個、root importと生成AxiomAuditを追加更新。
- 一時ファイルでの評価関手の有限(余)極限instanceとextの型合わせの失敗は修正済み。
  完成モジュールのコンパイルエラー・監査エラーはなし。
- 差分：`runs/rightmodule-abelian-20261008-unit3.patch`。
- 利用先：`rightModule_epi_iff_surjective`とYonedaによるrepresentableの射影性、
  `rightModule_exact_iff_range_eq_ker`による(1.6)の成分wiseな完全性の検証。
- 残る証明義務：射影性、radicalとs_v、四項分解とminimality、実際のExt条件、
  presheafモデルと直和・局所単位元付き加群の明示的同値。主定理は未実装・未証明。

PRのbase更新：リモートでPR #1が2026-10-08T00:18:35Zに既にマージ済みと確認し、
PR #2のbaseをmainへ変更。mainの観測HEADは`0d806291edbaf56b4ff30b77e45d2a632a207a27`。
本タスクはmainへpush・マージしていない。

## 引継ぎの確定・リモート検証

今回の数学的目標は既存presheafモデル上で完成。12 theorem・4 def・14 named instanceを追加。
README、AGENTS、HANDOFF、STATUS、GAPSを現行結果と残る義務に合わせて更新。
元の14数学モジュール・PDF・旧4ログ・初期161異なる宣言を照合し、終了0。
checkpoints/・recovery/の変更なし。詳細はverification/rightmodule_integrity.json。
git diff --checkは終了0。保存したraw patchの空白context markerを保つため、
.gitattributesはruns/*.patchだけを空白検査から除外（ソース・文書には検査を適用）。
整合性検査の初回終了1は保存ログのパス指定誤りで、正しいverification/下で再実行して解消。

数学的実装の最終コミット：`f8e7ce0c4336be1d7360a64ef8d0b631f807c982`、push終了0。
このコミットのpush/pull_request CIは双方success、全検証段階終了0。
各artifactに今回のrunログと固定Leanのsetupログの12ファイルを保存。

- push: https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37708459140
  UTC 2026-10-08T00:35:09.589226+00:00 → 2026-10-08T00:38:20.817504+00:00、191.228272秒、終了0。
  artifact: https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37708459140/artifacts/11520900890 （12ファイル）。

- pull_request: https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37708463929
  UTC 2026-10-08T00:34:39.307991+00:00 → 2026-10-08T00:37:38.079317+00:00、178.771325秒、終了0。
  artifact: https://github.com/uedakazushi/as-ginzburg-lean/actions/runs/37708463929/artifacts/11520603315 （12ファイル）。

Actionsログから得た各段階の終了コード・時刻・実測秒とartifactメタデータは
verification/rightmodule_github_ci_evidence.json。今回の成功を過去の記録から流用していない。
PR #2はmainをbaseとするDraft。mainへpush・マージしていない。
最後の追加コミットは引継ぎ・整合性証拠・差分ファイル属性の記録のみで、検証済みのLean実装は無変更。

残存：既存lint警告。新規数学のコンパイル・監査エラーはなし。
未実装：representableの射影性、s_v、(1.6)の実際の最小完全分解、実際のExt、
直和・局所単位元付き加群モデルとの明示的同値。主定理3.2・系5.2の形式的文と証明も未実装。
周期性をAS条件に追加しない。この目標を超える数学的作業には別の明示的な指示が必要。

実測開始：2026-10-08T00:20:15+00:00（秒精度）。
実装・検査・引継ぎの記録確定時刻：2026-10-08T00:40:14.171377+00:00。
記録確定までの実測所要時間：1199.171377秒（UTC時計差）。
記録コミット・pushはこの時刻の後に行い、その後の終了観測と全区間の時間はPR本文と最終報告に記載する。
過去の稼働時間を推測していない。検証時間はタスク全体の時間と区別する。
