(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_A_4_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_4_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_4_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |interface_3_B_21_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_4_B_21_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_5_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_4_B_21_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_6_constructor_20_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_7_C_38_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_8_C_38_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_9_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_8_C_38_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_10_constructor_37_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_11_D_59_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_12_D_59_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_13_D_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_12_D_59_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_14_constructor_20_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_15_constructor_37_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_16_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_17_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_18_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_0 x_3_0))) (contract_initializer_entry_18_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_0))))


(declare-fun |contract_initializer_after_init_19_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_entry_18_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 1) true)))) true) (contract_initializer_after_init_19_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_after_init_19_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_17_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_20_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_20_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (implicit_constructor_entry_20_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (contract_initializer_17_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_2_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (implicit_constructor_entry_20_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= error_1 0) (and (contract_initializer_17_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))) true) (summary_constructor_2_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (summary_constructor_2_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_4_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_21_constructor_20_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_22__19_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_21_constructor_20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_21_constructor_20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_22__19_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_23_return_constructor_20_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_24_constructor_20_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_22__19_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_12_1 (= expr_10_0 expr_11_0)) (and (=> true true) (and (= expr_11_0 1) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_0 x_3_1) true)))))) (and (not expr_12_1) (= error_1 1))) (block_24_constructor_20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_24_constructor_20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_6_constructor_20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_22__19_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_17_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 expr_16_0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_3_1) (and (=> true true) (and (= expr_16_0 2) (and (= error_1 error_0) (and (= expr_12_1 (= expr_10_0 expr_11_0)) (and (=> true true) (and (= expr_11_0 1) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_0 x_3_1) true)))))))))))))) true) (block_23_return_constructor_20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_23_return_constructor_20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_6_constructor_20_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_25_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_26_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_26_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_27_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_26_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_27_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_27_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_6_constructor_20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_25_B_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_27_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_6_constructor_20_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_25_B_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |contract_initializer_28_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_29_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_3_2 x_3_0))) (contract_initializer_entry_29_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(declare-fun |contract_initializer_after_init_30_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_29_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 1) true)))) true) (contract_initializer_after_init_30_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_30_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_28_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_31_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_31_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_31_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_28_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_5_B_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_31_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_25_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_28_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))) (> error_2 0)) (summary_constructor_5_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_31_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_2 0) (and (contract_initializer_25_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_28_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))))) true) (summary_constructor_5_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (summary_constructor_5_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_3_B_21_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_32_constructor_37_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_33__36_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_32_constructor_37_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_32_constructor_37_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_33__36_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_34_return_constructor_37_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_35_constructor_37_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_33__36_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 1) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_3_1) true)))))) (and (not expr_29_1) (= error_1 2))) (block_35_constructor_37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_35_constructor_37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_10_constructor_37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_33__36_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_34_1) (and (=> true (and (>= expr_34_1 0) (<= expr_34_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_1 expr_33_0) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 x_3_1) (and (=> true true) (and (= expr_33_0 3) (and (= error_1 error_0) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 1) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_3_1) true)))))))))))))) true) (block_34_return_constructor_37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_34_return_constructor_37_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_10_constructor_37_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_36_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_37_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_37_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_38_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_37_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_38_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_38_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_10_constructor_37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_36_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_38_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_10_constructor_37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_36_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |contract_initializer_39_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_40_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_3_2 x_3_0))) (contract_initializer_entry_40_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(declare-fun |contract_initializer_after_init_41_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_40_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 1) true)))) true) (contract_initializer_after_init_41_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_41_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_39_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_42_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_42_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_42_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_39_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_9_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_42_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_36_C_38_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_39_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))) (> error_2 0)) (summary_constructor_9_C_38_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_42_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_2 0) (and (contract_initializer_36_C_38_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_39_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))))) true) (summary_constructor_9_C_38_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (summary_constructor_9_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_7_C_38_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_43_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_44__57_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_43_constructor_58_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_43_constructor_58_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_44__57_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_45_return_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_46_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_44__57_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_48_1 (= expr_46_0 expr_47_0)) (and (=> true true) (and (= expr_47_0 3) (and (=> true (and (>= expr_46_0 0) (<= expr_46_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_46_0 x_3_1) true)))))) (and (not expr_48_1) (= error_1 3))) (block_46_constructor_58_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_46_constructor_58_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_16_constructor_58_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_47_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_44__57_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_54_1 (= expr_52_0 expr_53_0)) (and (=> true true) (and (= expr_53_0 4) (and (=> true (and (>= expr_52_0 0) (<= expr_52_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_52_0 x_3_1) (and (= error_1 error_0) (and (= expr_48_1 (= expr_46_0 expr_47_0)) (and (=> true true) (and (= expr_47_0 3) (and (=> true (and (>= expr_46_0 0) (<= expr_46_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_46_0 x_3_1) true)))))))))))) (and (not expr_54_1) (= error_2 4))) (block_47_constructor_58_59_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_47_constructor_58_59_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_16_constructor_58_59_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_44__57_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_2 error_1) (and (= expr_54_1 (= expr_52_0 expr_53_0)) (and (=> true true) (and (= expr_53_0 4) (and (=> true (and (>= expr_52_0 0) (<= expr_52_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_52_0 x_3_1) (and (= error_1 error_0) (and (= expr_48_1 (= expr_46_0 expr_47_0)) (and (=> true true) (and (= expr_47_0 3) (and (=> true (and (>= expr_46_0 0) (<= expr_46_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_46_0 x_3_1) true))))))))))))) true) (block_45_return_constructor_58_59_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_45_return_constructor_58_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_16_constructor_58_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_48_D_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_49_D_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_49_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_50_D_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_49_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_50_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_50_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_16_constructor_58_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_48_D_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_50_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_16_constructor_58_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_48_D_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_51_constructor_37_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_52__36_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_51_constructor_37_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_51_constructor_37_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_52__36_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_53_return_constructor_37_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_54_constructor_37_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_52__36_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 1) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_3_1) true)))))) (and (not expr_29_1) (= error_1 5))) (block_54_constructor_37_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_54_constructor_37_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_15_constructor_37_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_52__36_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_34_1) (and (=> true (and (>= expr_34_1 0) (<= expr_34_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_1 expr_33_0) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 x_3_1) (and (=> true true) (and (= expr_33_0 3) (and (= error_1 error_0) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 1) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_3_1) true)))))))))))))) true) (block_53_return_constructor_37_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_53_return_constructor_37_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_15_constructor_37_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_55_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_56_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_56_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_57_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_56_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_57_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_57_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_15_constructor_37_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_55_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_57_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_15_constructor_37_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_55_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_58_constructor_20_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_59__19_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_58_constructor_20_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_58_constructor_20_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_59__19_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_60_return_constructor_20_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_61_constructor_20_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_59__19_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_12_1 (= expr_10_0 expr_11_0)) (and (=> true true) (and (= expr_11_0 1) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_0 x_3_1) true)))))) (and (not expr_12_1) (= error_1 6))) (block_61_constructor_20_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_61_constructor_20_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_14_constructor_20_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_59__19_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_17_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 expr_16_0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_3_1) (and (=> true true) (and (= expr_16_0 2) (and (= error_1 error_0) (and (= expr_12_1 (= expr_10_0 expr_11_0)) (and (=> true true) (and (= expr_11_0 1) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_0 x_3_1) true)))))))))))))) true) (block_60_return_constructor_20_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_60_return_constructor_20_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_14_constructor_20_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_62_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_63_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_63_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_64_B_21_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_63_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_64_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_64_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_14_constructor_20_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_62_B_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_64_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_14_constructor_20_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_62_B_21_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |contract_initializer_65_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_66_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_3_2 x_3_0))) (contract_initializer_entry_66_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(declare-fun |contract_initializer_after_init_67_A_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_66_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 1) true)))) true) (contract_initializer_after_init_67_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_67_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_65_A_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_68_D_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_68_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_68_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_65_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_13_D_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_68_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_62_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_65_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))) (> error_2 0)) (summary_constructor_13_D_59_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (implicit_constructor_entry_68_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_55_C_38_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_3_3 state_4 x_3_4) (and (= error_2 0) (and (contract_initializer_62_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_65_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))))) (> error_3 0)) (summary_constructor_13_D_59_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_4 x_3_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (implicit_constructor_entry_68_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_48_D_59_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 x_3_4 state_5 x_3_5) (and (= error_3 0) (and (contract_initializer_55_C_38_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_3_3 state_4 x_3_4) (and (= error_2 0) (and (contract_initializer_62_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_65_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))))))) (> error_4 0)) (summary_constructor_13_D_59_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_5 x_3_5))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (implicit_constructor_entry_68_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_4 0) (and (contract_initializer_48_D_59_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 x_3_4 state_5 x_3_5) (and (= error_3 0) (and (contract_initializer_55_C_38_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_3_3 state_4 x_3_4) (and (= error_2 0) (and (contract_initializer_62_B_21_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_65_A_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))))))))) true) (summary_constructor_13_D_59_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_5 x_3_5))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_13_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_11_D_59_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |error_target_7_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_5_B_21_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_7_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_13_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_7_0)))


(declare-fun |error_target_8_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_9_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 2))) error_target_8_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_13_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 2))) error_target_8_0)))


(declare-fun |error_target_9_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_13_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 3))) error_target_9_0)))


(declare-fun |error_target_10_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_13_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 4))) error_target_10_0)))


(declare-fun |error_target_11_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_13_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 5))) error_target_11_0)))


(declare-fun |error_target_12_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> (and (and (summary_constructor_13_D_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 6))) error_target_12_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_2_0 Int) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Int) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int) (x_3_5 Int))
(=> error_target_12_0 false)))
(check-sat)