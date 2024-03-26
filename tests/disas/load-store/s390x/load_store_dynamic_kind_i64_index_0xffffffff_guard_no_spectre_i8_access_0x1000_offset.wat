;;! target = "s390x"
;;! test = "compile"
;;! flags = " -C cranelift-enable-heap-access-spectre-mitigation=false -W memory64 -O static-memory-maximum-size=0 -O static-memory-guard-size=4294967295 -O dynamic-memory-guard-size=4294967295"

;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;; !!! GENERATED BY 'make-load-store-tests.sh' DO NOT EDIT !!!
;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

(module
  (memory i64 1)

  (func (export "do_store") (param i64 i32)
    local.get 0
    local.get 1
    i32.store8 offset=0x1000)

  (func (export "do_load") (param i64) (result i32)
    local.get 0
    i32.load8_u offset=0x1000))

;; wasm[0]::function[0]:
;;    0: stmg    %r14, %r15, 0x70(%r15)
;;    6: lgr     %r1, %r15
;;    a: aghi    %r15, -0xa0
;;    e: stg     %r1, 0(%r15)
;;   14: lg      %r3, 0x58(%r2)
;;   1a: clgr    %r4, %r3
;;   1e: jgh     0x3a
;;   24: ag      %r4, 0x50(%r2)
;;   2a: lghi    %r3, 0x1000
;;   2e: stc     %r5, 0(%r3, %r4)
;;   32: lmg     %r14, %r15, 0x110(%r15)
;;   38: br      %r14
;;   3a: .byte   0x00, 0x00
;;
;; wasm[0]::function[1]:
;;   3c: stmg    %r14, %r15, 0x70(%r15)
;;   42: lgr     %r1, %r15
;;   46: aghi    %r15, -0xa0
;;   4a: stg     %r1, 0(%r15)
;;   50: lg      %r5, 0x58(%r2)
;;   56: clgr    %r4, %r5
;;   5a: jgh     0x78
;;   60: ag      %r4, 0x50(%r2)
;;   66: lghi    %r3, 0x1000
;;   6a: llc     %r2, 0(%r3, %r4)
;;   70: lmg     %r14, %r15, 0x110(%r15)
;;   76: br      %r14
;;   78: .byte   0x00, 0x00
