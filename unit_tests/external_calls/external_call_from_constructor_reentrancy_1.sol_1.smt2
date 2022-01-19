(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_D_9_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_D_9_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_D_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_D_9_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_ext__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |summary_4_function_ext__8_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_D_9_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_ext__8_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 c_3_0 state_2 c_3_1 _6_1))) (nondet_interface_1_D_9_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_5_C_48_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_6_C_48_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_7_C_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int))
(=> (= error_1 0) (nondet_interface_6_C_48_0 error_1 this_0 abi_0 crypto_0 state_0 x_11_0 state_0 x_11_0))))


(declare-fun |summary_8_function_s__21_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_9_function_s__21_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_x_13_0 Int) (_x_13_1 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int))
(=> (and (and (nondet_interface_6_C_48_0 error_1 this_0 abi_0 crypto_0 state_0 x_11_0 state_1 x_11_1) true) (and (= error_1 0) (summary_9_function_s__21_48_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_11_1 _x_13_0 state_2 x_11_2 _x_13_1))) (nondet_interface_6_C_48_0 error_2 this_0 abi_0 crypto_0 state_0 x_11_0 state_2 x_11_2))))


(declare-fun |summary_10_constructor_47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_x_13_0 Int) (_x_13_1 Int) (a_28_1 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int))
(=> (and true (= error_0 0)) (summary_3_function_ext__8_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 c_3_0 state_1 c_3_1 _6_1))))


(declare-fun |contract_initializer_11_D_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_12_D_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_6_1 Int) (_x_13_0 Int) (_x_13_1 Int) (a_28_1 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_12_D_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_13_D_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_6_1 Int) (_x_13_0 Int) (_x_13_1 Int) (a_28_1 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int))
(=> (and (and (contract_initializer_entry_12_D_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_13_D_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_6_1 Int) (_x_13_0 Int) (_x_13_1 Int) (a_28_1 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int))
(=> (and (and (contract_initializer_after_init_13_D_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_11_D_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_14_D_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_6_1 Int) (_x_13_0 Int) (_x_13_1 Int) (a_28_1 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_14_D_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_6_1 Int) (_x_13_0 Int) (_x_13_1 Int) (a_28_1 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int))
(=> (and (and (implicit_constructor_entry_14_D_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_11_D_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_D_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_6_1 Int) (_x_13_0 Int) (_x_13_1 Int) (a_28_1 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int))
(=> (and (and (implicit_constructor_entry_14_D_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_11_D_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_D_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |block_15_function_s__21_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_16_s_20_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(block_15_function_s__21_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_1 x_11_1 _x_13_1)))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_15_function_s__21_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_1 x_11_1 _x_13_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_11_1 x_11_0))) (and true (= _x_13_1 _x_13_0))) true)) true) (block_16_s_20_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_1 x_11_1 _x_13_1))))


(declare-fun |block_17_return_function_s__21_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_16_s_20_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_1 x_11_1 _x_13_1) (and (= x_11_2 expr_18_1) (and (=> true (and (>= expr_18_1 0) (<= expr_18_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_1 expr_17_0) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 x_11_1) (and (=> true (and (>= expr_17_0 0) (<= expr_17_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_0 _x_13_1) (and (and (>= _x_13_1 0) (<= _x_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_17_return_function_s__21_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_1 x_11_2 _x_13_1))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_17_return_function_s__21_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_1 x_11_1 _x_13_1) true) true) (summary_8_function_s__21_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_1 x_11_1 _x_13_1))))


(declare-fun |block_18_function_s__21_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(block_18_function_s__21_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_1 x_11_1 _x_13_1)))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_18_function_s__21_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_1 x_11_1 _x_13_1) (and (summary_8_function_s__21_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_11_1 _x_13_1 state_3 x_11_2 _x_13_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 1391449733)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 82)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 239)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 214)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 133)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_11_1 x_11_0))) (and true (= _x_13_1 _x_13_0))) true))))))) true) (summary_9_function_s__21_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_3 x_11_2 _x_13_2))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (interface_5_C_48_0 this_0 abi_0 crypto_0 state_0 x_11_0) true) (and (summary_9_function_s__21_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 _x_13_0 state_1 x_11_1 _x_13_1) (= error_0 0))) (interface_5_C_48_0 this_0 abi_0 crypto_0 state_1 x_11_1))))


(declare-fun |block_19_constructor_47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_20__46_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(block_19_constructor_47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_1)))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_19_constructor_47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_11_1 x_11_0))) (and true (= d_24_1 d_24_0))) true)) true) (block_20__46_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_1))))


(declare-fun |block_21_return_constructor_47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_22_constructor_47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_20__46_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_1) (and (= expr_37_1 (= expr_35_0 expr_36_0)) (and (=> true true) (and (= expr_36_0 0) (and (=> true (and (>= expr_35_0 0) (<= expr_35_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_35_0 x_11_1) (and (= a_28_2 expr_32_1) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_1 _6_4) (and (=> true true) (and (= expr_31_0 this_0) (and (=> true true) (and (= expr_29_0 d_24_1) (and (and (>= d_24_1 0) (<= d_24_1 1461501637330902918203684832716283019655932542975)) (and (= a_28_1 0) true))))))))))))))) (and (not expr_37_1) (= error_1 1))) (block_22_constructor_47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_2))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (block_22_constructor_47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_2) (summary_10_constructor_47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1))))


(declare-fun |block_23_constructor_47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_20__46_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_1) (and (= expr_43_1 (= expr_41_0 expr_42_0)) (and (=> true true) (and (= expr_42_0 2) (and (=> true (and (>= expr_41_0 0) (<= expr_41_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_41_0 a_28_2) (and (= error_1 error_0) (and (= expr_37_1 (= expr_35_0 expr_36_0)) (and (=> true true) (and (= expr_36_0 0) (and (=> true (and (>= expr_35_0 0) (<= expr_35_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_35_0 x_11_1) (and (= a_28_2 expr_32_1) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_1 _6_4) (and (=> true true) (and (= expr_31_0 this_0) (and (=> true true) (and (= expr_29_0 d_24_1) (and (and (>= d_24_1 0) (<= d_24_1 1461501637330902918203684832716283019655932542975)) (and (= a_28_1 0) true))))))))))))))))))))) (and (not expr_43_1) (= error_2 2))) (block_23_constructor_47_48_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_2))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (block_23_constructor_47_48_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_2) (summary_10_constructor_47_48_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_20__46_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_1) (and (= error_2 error_1) (and (= expr_43_1 (= expr_41_0 expr_42_0)) (and (=> true true) (and (= expr_42_0 2) (and (=> true (and (>= expr_41_0 0) (<= expr_41_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_41_0 a_28_2) (and (= error_1 error_0) (and (= expr_37_1 (= expr_35_0 expr_36_0)) (and (=> true true) (and (= expr_36_0 0) (and (=> true (and (>= expr_35_0 0) (<= expr_35_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_35_0 x_11_1) (and (= a_28_2 expr_32_1) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_1 _6_4) (and (=> true true) (and (= expr_31_0 this_0) (and (=> true true) (and (= expr_29_0 d_24_1) (and (and (>= d_24_1 0) (<= d_24_1 1461501637330902918203684832716283019655932542975)) (and (= a_28_1 0) true)))))))))))))))))))))) true) (block_21_return_constructor_47_48_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_2))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (block_21_return_constructor_47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1 a_28_1) true) true) (summary_10_constructor_47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1))))


(declare-fun |contract_initializer_24_C_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_25_C_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_11_1 x_11_0))) (and true (= d_24_1 d_24_0))) (contract_initializer_entry_25_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1))))


(declare-fun |contract_initializer_after_init_26_C_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (contract_initializer_entry_25_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1) true) true) (contract_initializer_after_init_26_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (contract_initializer_after_init_26_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1) (and (summary_10_constructor_47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_11_1 d_24_1 state_2 x_11_2 d_24_2) true)) (> error_1 0)) (contract_initializer_24_C_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_2 x_11_2 d_24_2))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (contract_initializer_after_init_26_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_1) (and (= error_1 0) (and (summary_10_constructor_47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_11_1 d_24_1 state_2 x_11_2 d_24_2) true))) true) (contract_initializer_24_C_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_2 x_11_2 d_24_2))))


(declare-fun |implicit_constructor_entry_27_C_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_11_2 x_11_0))) (and true (= d_24_2 d_24_0))) (and true (= x_11_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_27_C_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_2 x_11_2 d_24_2))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (implicit_constructor_entry_27_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_2) (and (contract_initializer_24_C_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_11_1 d_24_2 state_2 x_11_2 d_24_3) true)) (> error_1 0)) (summary_constructor_7_C_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_2 x_11_2 d_24_3))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (implicit_constructor_entry_27_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_2) (and (= error_1 0) (and (contract_initializer_24_C_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_11_1 d_24_2 state_2 x_11_2 d_24_3) true))) true) (summary_constructor_7_C_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_2 x_11_2 d_24_3))))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (summary_constructor_7_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_C_48_0 this_0 abi_0 crypto_0 state_1 x_11_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_6_5 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (c_3_4 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (d_24_4 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> (and (and (summary_constructor_7_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_11_0 d_24_0 state_1 x_11_1 d_24_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (_6_1 Int) (_6_2 Int) (_6_3 Int) (_6_4 Int) (_6_5 Int) (_x_13_0 Int) (_x_13_1 Int) (_x_13_2 Int) (_x_13_3 Int) (a_28_0 Int) (a_28_1 Int) (a_28_2 Int) (a_28_3 Int) (abi_0 |abi_type|) (c_3_0 Int) (c_3_1 Int) (c_3_2 Int) (c_3_3 Int) (c_3_4 Int) (crypto_0 |crypto_type|) (d_24_0 Int) (d_24_1 Int) (d_24_2 Int) (d_24_3 Int) (d_24_4 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Int) (expr_29_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_35_0 Int) (expr_36_0 Int) (expr_37_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_11_0 Int) (x_11_1 Int) (x_11_2 Int) (x_11_3 Int))
(=> error_target_3_0 false)))
(check-sat)