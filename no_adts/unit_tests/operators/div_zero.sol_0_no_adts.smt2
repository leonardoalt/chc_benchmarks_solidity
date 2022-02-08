; Auto-generated flattened instance without ADTs.
(set-logic HORN)
(declare-fun interface_0_C_9_0 (Int (Array Int (Array Int (Array Int (Array Int Int)))) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) (Array Int Int) Int Int) Bool)
(declare-fun nondet_interface_1_C_9_0 (Int Int (Array Int (Array Int (Array Int (Array Int Int)))) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) (Array Int Int) Int Int (Array Int Int) Int Int) Bool)
(declare-fun summary_constructor_2_C_9_0 (Int Int (Array Int (Array Int (Array Int (Array Int Int)))) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int) Bool)
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (state_0_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (z_3_0 Int)) (=> (= error_0 0) (nondet_interface_1_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 state_0_balances_0 z_3_0 x_8_0 state_0_balances_0 z_3_0 x_8_0))))
(declare-fun contract_initializer_3_C_9_0 (Int Int (Array Int (Array Int (Array Int (Array Int Int)))) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int) Bool)
(declare-fun contract_initializer_entry_4_C_9_0 (Int Int (Array Int (Array Int (Array Int (Array Int Int)))) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int) Bool)
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (z_3_0 Int) (z_3_1 Int)) (=> (and (and (= state_1_balances_0 state_0_balances_0) (= error_0 0)) (and (and true (= z_3_0 z_3_0)) (= x_8_0 x_8_0))) (contract_initializer_entry_4_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_0 x_8_0))))
(declare-fun local_error_5_C_9_0 (Int Int (Array Int (Array Int (Array Int (Array Int Int)))) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int) Bool)
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int)) (=> (and (and (contract_initializer_entry_4_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_1 x_8_1) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 z_3_2) (and (=> true true) (and (= expr_5_0 2) (and (= z_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 0) true)))))))) (and (= expr_6_0 0) (= error_1 1))) (local_error_5_C_9_0 error_1 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_2 x_8_1))))
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int)) (=> (local_error_5_C_9_0 error_1 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_2 x_8_1) (contract_initializer_3_C_9_0 error_1 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_2 x_8_1))))
(declare-fun contract_initializer_after_init_6_C_9_0 (Int Int (Array Int (Array Int (Array Int (Array Int Int)))) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int) Bool)
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int)) (=> (and (and (contract_initializer_entry_4_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_1 x_8_1) (and (= x_8_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 (div expr_5_0 expr_6_0)) (and (= error_1 error_0) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 z_3_2) (and (=> true true) (and (= expr_5_0 2) (and (= z_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 0) true)))))))))))) true) (contract_initializer_after_init_6_C_9_0 error_1 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_2 x_8_2))))
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int)) (=> (and (and (contract_initializer_after_init_6_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_1 x_8_1) true) true) (contract_initializer_3_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_1 x_8_1))))
(declare-fun implicit_constructor_entry_7_C_9_0 (Int Int (Array Int (Array Int (Array Int (Array Int Int)))) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) (Array (Array Int Int) (Array Int Int)) Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int Int) Bool)
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int)) (=> (and (and (and (and (= state_1_balances_0 state_0_balances_0) (= error_0 0)) (and (and true (= z_3_1 z_3_0)) (= x_8_1 x_8_0))) (and (and true (= z_3_1 0)) (= x_8_1 0))) (>= (select state_1_balances_0 this_0) tx_0_msg.value_14)) (implicit_constructor_entry_7_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_1 x_8_1))))
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (state_2_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int)) (=> (and (and (implicit_constructor_entry_7_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_1 x_8_1) (and (contract_initializer_3_C_9_0 error_1 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_1_balances_0 state_2_balances_0 z_3_1 x_8_1 z_3_2 x_8_2) true)) (> error_1 0)) (summary_constructor_2_C_9_0 error_1 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_2_balances_0 z_3_0 x_8_0 z_3_2 x_8_2))))
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (state_2_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int)) (=> (and (and (implicit_constructor_entry_7_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_1 x_8_1) (and (= error_1 0) (and (contract_initializer_3_C_9_0 error_1 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_1_balances_0 state_2_balances_0 z_3_1 x_8_1 z_3_2 x_8_2) true))) true) (summary_constructor_2_C_9_0 error_1 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_2_balances_0 z_3_0 x_8_0 z_3_2 x_8_2))))
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (state_2_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int)) (=> (and (and (summary_constructor_2_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_1 x_8_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= tx_0_block.basefee_3 0) (<= tx_0_block.basefee_3 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= tx_0_block.chainid_4 0) (<= tx_0_block.chainid_4 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_block.coinbase_5 0) (<= tx_0_block.coinbase_5 1461501637330902918203684832716283019655932542975))) (and (>= tx_0_block.difficulty_6 0) (<= tx_0_block.difficulty_6 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_block.gaslimit_7 0) (<= tx_0_block.gaslimit_7 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_block.number_8 0) (<= tx_0_block.number_8 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_block.timestamp_9 0) (<= tx_0_block.timestamp_9 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_msg.sender_12 0) (<= tx_0_msg.sender_12 1461501637330902918203684832716283019655932542975))) (and (>= tx_0_msg.value_14 0) (<= tx_0_msg.value_14 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_tx.origin_16 0) (<= tx_0_tx.origin_16 1461501637330902918203684832716283019655932542975))) (and (>= tx_0_tx.gasprice_15 0) (<= tx_0_tx.gasprice_15 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= tx_0_msg.value_14 0)) (= error_0 0))) (interface_0_C_9_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 state_1_balances_0 z_3_1 x_8_1))))
(declare-fun error_target_2_0 () Bool)
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (state_2_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int)) (=> (and (and (summary_constructor_2_C_9_0 error_0 this_0 crypto_0_ecrecover_21 crypto_0_keccak256_22 crypto_0_ripemd160_23 crypto_0_sha256_24 tx_0_block.basefee_3 tx_0_block.chainid_4 tx_0_block.coinbase_5 tx_0_block.difficulty_6 tx_0_block.gaslimit_7 tx_0_block.number_8 tx_0_block.timestamp_9 tx_0_blockhash_10 tx_0_msg.data_11_bytes_tuple_accessor_array_1 tx_0_msg.data_11_bytes_tuple_accessor_length_2 tx_0_msg.sender_12 tx_0_msg.sig_13 tx_0_msg.value_14 tx_0_tx.gasprice_15 tx_0_tx.origin_16 state_0_balances_0 state_1_balances_0 z_3_0 x_8_0 z_3_1 x_8_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= tx_0_block.basefee_3 0) (<= tx_0_block.basefee_3 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= tx_0_block.chainid_4 0) (<= tx_0_block.chainid_4 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_block.coinbase_5 0) (<= tx_0_block.coinbase_5 1461501637330902918203684832716283019655932542975))) (and (>= tx_0_block.difficulty_6 0) (<= tx_0_block.difficulty_6 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_block.gaslimit_7 0) (<= tx_0_block.gaslimit_7 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_block.number_8 0) (<= tx_0_block.number_8 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_block.timestamp_9 0) (<= tx_0_block.timestamp_9 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_msg.sender_12 0) (<= tx_0_msg.sender_12 1461501637330902918203684832716283019655932542975))) (and (>= tx_0_msg.value_14 0) (<= tx_0_msg.value_14 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= tx_0_tx.origin_16 0) (<= tx_0_tx.origin_16 1461501637330902918203684832716283019655932542975))) (and (>= tx_0_tx.gasprice_15 0) (<= tx_0_tx.gasprice_15 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= tx_0_msg.value_14 0)) (= error_0 1))) error_target_2_0)))
(assert (forall ((crypto_0_ecrecover_21 (Array Int (Array Int (Array Int (Array Int Int))))) (crypto_0_keccak256_22 (Array (Array Int Int) (Array Int Int))) (crypto_0_ripemd160_23 (Array (Array Int Int) (Array Int Int))) (crypto_0_sha256_24 (Array (Array Int Int) (Array Int Int))) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0_balances_0 (Array Int Int)) (state_1_balances_0 (Array Int Int)) (state_2_balances_0 (Array Int Int)) (this_0 Int) (tx_0_block.basefee_3 Int) (tx_0_block.chainid_4 Int) (tx_0_block.coinbase_5 Int) (tx_0_block.difficulty_6 Int) (tx_0_block.gaslimit_7 Int) (tx_0_block.number_8 Int) (tx_0_block.timestamp_9 Int) (tx_0_blockhash_10 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_array_1 (Array Int Int)) (tx_0_msg.data_11_bytes_tuple_accessor_length_2 Int) (tx_0_msg.sender_12 Int) (tx_0_msg.sig_13 Int) (tx_0_msg.value_14 Int) (tx_0_tx.gasprice_15 Int) (tx_0_tx.origin_16 Int) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int)) (=> error_target_2_0 false)))
(check-sat)

