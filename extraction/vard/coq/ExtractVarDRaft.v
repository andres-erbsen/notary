Require Import Net.
Require Import Arith.
Require Import NPeano.
Require Import PeanoNat.
Import Nat.
Require Import List.
Require Import Util.
Require Import VarD.
Require Import VarDRaft.
Require Import Ascii.
Require Import String.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Extract Inlined Constant length => "List.length".
Extract Inlined Constant negb => "not".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant filter => "List.filter".
Extract Inlined Constant fold_left => "(fun a b c -> List.fold_left a c b)".
Extract Inlined Constant in_dec => "(fun h -> List.mem)".
Extract Inlined Constant leb => "(<=)".
Extract Inlined Constant ltb => "(<)".
Extract Inlined Constant pred => "(fun n -> if n <= 0 then 0 else n - 1)".

Extract Inlined Constant fin => int.

Extract Inlined Constant fin_eq_dec => "(fun _ -> (=))".
Extract Inlined Constant all_fin => "(fun n -> (Obj.magic (seq 1 n)))".

Extraction "VarDRaft.ml" seq vard_raft_base_params vard_raft_multi_params vard_raft_failure_params.
