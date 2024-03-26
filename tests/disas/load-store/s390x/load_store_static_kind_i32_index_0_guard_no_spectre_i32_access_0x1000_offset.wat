;;! target = "s390x"
;;! test = "compile"
;;! flags = " -C cranelift-enable-heap-access-spectre-mitigation=false -O static-memory-forced -O static-memory-guard-size=0 -O dynamic-memory-guard-size=0"

;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;; !!! GENERATED BY 'make-load-store-tests.sh' DO NOT EDIT !!!
;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

(module
  (memory i32 1)

  (func (export "do_store") (param i32 i32)
    local.get 0
    local.get 1
    i32.store offset=0x1000)

  (func (export "do_load") (param i32) (result i32)
    local.get 0
    i32.load offset=0x1000))

;; wasm[0]::function[0]:
;;    0: stmg    %r14, %r15, 0x70(%r15)
;;    6: lgr     %r1, %r15
;;    a: aghi    %r15, -0xa0
;;    e: stg     %r1, 0(%r15)
;;   14: llgfr   %r4, %r4
;;   18: clgfi   %r4, 0xffffeffc
;;   1e: jgh     0x3c
;;   24: ag      %r4, 0x50(%r2)
;;   2a: lghi    %r3, 0x1000
;;   2e: strv    %r5, 0(%r3, %r4)
;;   34: lmg     %r14, %r15, 0x110(%r15)
;;   3a: br      %r14
;;   3c: .byte   0x00, 0x00
;;
;; wasm[0]::function[1]:
;;   40: stmg    %r14, %r15, 0x70(%r15)
;;   46: lgr     %r1, %r15
;;   4a: aghi    %r15, -0xa0
;;   4e: stg     %r1, 0(%r15)
;;   54: llgfr   %r4, %r4
;;   58: clgfi   %r4, 0xffffeffc
;;   5e: jgh     0x7c
;;   64: ag      %r4, 0x50(%r2)
;;   6a: lghi    %r3, 0x1000
;;   6e: lrv     %r2, 0(%r3, %r4)
;;   74: lmg     %r14, %r15, 0x110(%r15)
;;   7a: br      %r14
;;   7c: .byte   0x00, 0x00
