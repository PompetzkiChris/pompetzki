From RDNUM Require Import RDNUMSource RDNUMTools RDNUMCalls RDNUMStops RDNUMReaders RDNUMNumber RDNUMWordBounds RDNUMPolicy RDNUMEntry RDNUMRefusal RDNUMDelimiter RDNUMComplete RDNUMLexical RDNUMBuffer RDNUMInvariants RDNUMWordOperations.
Check @RDNUM_leading_zero.
Check @RDNUM_significant_digit.
Check @RDNUM_first_nonzero_digit.
Check @RDNUM_thirteenth_significant_refused.
Check @number_limit_no_accumulator_update.
Check @SKIPWS_success.
Check @ENDTOK_success.
Check @ENDTOK_failure.
Check @RDNUM_finish_success.
Check @checked_source_accumulator_signed64.
Check @source_cursor_subtraction_signed64.
Check @evals_call.
Check @RDNUM_source_sequence.
Check @scan_state_decimal_correspondence.
Check @RDNUM_source_refines_decimal.
Check @RDNUM_entry_decimal_success.
Check @RDNUM_source_sequence_refusal.
Check @RDNUM_empty_refused.
Check @RDNUM_bad_delimiter_refused.
Check @RDNUM_entry_policy_iff.
Check @lexical_entry_view.
Check @RDNUM_buffer_parse_success.
Check @RDNUM_buffer_parse_failure.
Check @RDNUM_buffer_returns_iff.
Check @RDNUM_buffer_stops_iff.
Check @scan_state_accumulator_invariant.
Check @source_prefix_next_arithmetic_fits.
Check @RDNUM_buffer_failure_input_unchanged.
Check @source_cursor_increment_signed64.
Check @source_scratch_operations_signed64.
Check @source_diagnostic_heap_signed64.
Check @evals_stop_extension.
Check @RDNUM_entry_policy_refusal.
Print Assumptions RDNUM_leading_zero.
Print Assumptions RDNUM_significant_digit.
Print Assumptions RDNUM_first_nonzero_digit.
Print Assumptions RDNUM_thirteenth_significant_refused.
Print Assumptions number_limit_no_accumulator_update.
Print Assumptions SKIPWS_success.
Print Assumptions ENDTOK_success.
Print Assumptions ENDTOK_failure.
Print Assumptions RDNUM_finish_success.
Print Assumptions checked_source_accumulator_signed64.
Print Assumptions source_cursor_subtraction_signed64.
Print Assumptions evals_call.
Print Assumptions RDNUM_source_sequence.
Print Assumptions scan_state_decimal_correspondence.
Print Assumptions RDNUM_source_refines_decimal.
Print Assumptions RDNUM_entry_decimal_success.
Print Assumptions RDNUM_source_sequence_refusal.
Print Assumptions RDNUM_empty_refused.
Print Assumptions RDNUM_bad_delimiter_refused.
Print Assumptions RDNUM_entry_policy_iff.
Print Assumptions lexical_entry_view.
Print Assumptions RDNUM_buffer_parse_success.
Print Assumptions RDNUM_buffer_parse_failure.
Print Assumptions RDNUM_buffer_returns_iff.
Print Assumptions RDNUM_buffer_stops_iff.
Print Assumptions scan_state_accumulator_invariant.
Print Assumptions source_prefix_next_arithmetic_fits.
Print Assumptions RDNUM_buffer_failure_input_unchanged.
Print Assumptions source_cursor_increment_signed64.
Print Assumptions source_scratch_operations_signed64.
Print Assumptions source_diagnostic_heap_signed64.
Print Assumptions evals_stop_extension.
Print Assumptions RDNUM_entry_policy_refusal.
