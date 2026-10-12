(* Exact new bridge declaration types and kernel assumptions. *)
From WordBridge Require Import PmpWordSub NativeWordSub AddressBridge.
Set Printing Depth 1000.
Set Printing Width 120.
Set Printing Implicit.
About WordBridge.PmpWordSub.PMP_sub_instruction.
Print Assumptions WordBridge.PmpWordSub.PMP_sub_instruction.
About WordBridge.PmpWordSub.PMP_sub_word_commutes.
Print Assumptions WordBridge.PmpWordSub.PMP_sub_word_commutes.
About WordBridge.PmpWordSub.PMP_sub_word_decode.
Print Assumptions WordBridge.PmpWordSub.PMP_sub_word_decode.
About WordBridge.PmpWordSub.PMP_negative_word_commutes.
Print Assumptions WordBridge.PmpWordSub.PMP_negative_word_commutes.
About WordBridge.PmpWordSub.RECORDCOUNT_words_exact.
Print Assumptions WordBridge.PmpWordSub.RECORDCOUNT_words_exact.
About WordBridge.PmpWordSub.RECORDCOUNT_word_decode.
Print Assumptions WordBridge.PmpWordSub.RECORDCOUNT_word_decode.
About WordBridge.PmpWordSub.RECORDCOUNT_word_test.
Print Assumptions WordBridge.PmpWordSub.RECORDCOUNT_word_test.
About WordBridge.PmpWordSub.RECORDCOUNT_word_control.
Print Assumptions WordBridge.PmpWordSub.RECORDCOUNT_word_control.
About WordBridge.PmpWordSub.RECORDCOUNT_signed_models_agree.
Print Assumptions WordBridge.PmpWordSub.RECORDCOUNT_signed_models_agree.
About WordBridge.PmpWordSub.RECORDCOUNT_word_execution_prefix.
Print Assumptions WordBridge.PmpWordSub.RECORDCOUNT_word_execution_prefix.
About WordBridge.PmpWordSub.RECORDCOUNT_return_word_result.
Print Assumptions WordBridge.PmpWordSub.RECORDCOUNT_return_word_result.
About WordBridge.PmpWordSub.RECORDCOUNT_failure_word_result.
Print Assumptions WordBridge.PmpWordSub.RECORDCOUNT_failure_word_result.
About WordBridge.NativeWordSub.native_w64_encode.
Print Assumptions WordBridge.NativeWordSub.native_w64_encode.
About WordBridge.NativeWordSub.native_w64_idempotent.
Print Assumptions WordBridge.NativeWordSub.native_w64_idempotent.
About WordBridge.NativeWordSub.native_sub_word.
Print Assumptions WordBridge.NativeWordSub.native_sub_word.
About WordBridge.NativeWordSub.native_msb_topbit.
Print Assumptions WordBridge.NativeWordSub.native_msb_topbit.
About WordBridge.NativeWordSub.native_reg_self.
Print Assumptions WordBridge.NativeWordSub.native_reg_self.
About WordBridge.NativeWordSub.native_reg_different.
Print Assumptions WordBridge.NativeWordSub.native_reg_different.
About WordBridge.NativeWordSub.native_getreg_updated.
Print Assumptions WordBridge.NativeWordSub.native_getreg_updated.
About WordBridge.NativeWordSub.native_sub_exec.
Print Assumptions WordBridge.NativeWordSub.native_sub_exec.
About WordBridge.NativeWordSub.native_sub_effects.
Print Assumptions WordBridge.NativeWordSub.native_sub_effects.
About WordBridge.NativeWordSub.native_sub_PMP_value.
Print Assumptions WordBridge.NativeWordSub.native_sub_PMP_value.
About WordBridge.NativeWordSub.native_test_self_exec.
Print Assumptions WordBridge.NativeWordSub.native_test_self_exec.
About WordBridge.NativeWordSub.native_test_self_effects.
Print Assumptions WordBridge.NativeWordSub.native_test_self_effects.
About WordBridge.NativeWordSub.RECORDCOUNT_native_negative_flag.
Print Assumptions WordBridge.NativeWordSub.RECORDCOUNT_native_negative_flag.
About WordBridge.NativeWordSub.native_sub_opcode_decodes.
Print Assumptions WordBridge.NativeWordSub.native_sub_opcode_decodes.
About WordBridge.NativeWordSub.native_test_opcode_decodes.
Print Assumptions WordBridge.NativeWordSub.native_test_opcode_decodes.
About WordBridge.AddressBridge.source_nonnegative_word_identity.
Print Assumptions WordBridge.AddressBridge.source_nonnegative_word_identity.
About WordBridge.AddressBridge.RECORDCOUNT_addresses_word_identity.
Print Assumptions WordBridge.AddressBridge.RECORDCOUNT_addresses_word_identity.
About WordBridge.AddressBridge.native_low_address_canonical.
Print Assumptions WordBridge.AddressBridge.native_low_address_canonical.
About WordBridge.AddressBridge.RECORDCOUNT_numeric_contract_not_canonical.
Print Assumptions WordBridge.AddressBridge.RECORDCOUNT_numeric_contract_not_canonical.
About WordBridge.AddressBridge.RECORDCOUNT_low_input_canonical.
Print Assumptions WordBridge.AddressBridge.RECORDCOUNT_low_input_canonical.
About WordBridge.AddressBridge.RECORDCOUNT_low_diagnostic_canonical.
Print Assumptions WordBridge.AddressBridge.RECORDCOUNT_low_diagnostic_canonical.
About WordBridge.AddressBridge.native_readable_region_allowed.
Print Assumptions WordBridge.AddressBridge.native_readable_region_allowed.
About WordBridge.AddressBridge.native_readbyte_agrees.
Print Assumptions WordBridge.AddressBridge.native_readbyte_agrees.
About WordBridge.AddressBridge.RECORDCOUNT_native_input_byte.
Print Assumptions WordBridge.AddressBridge.RECORDCOUNT_native_input_byte.
