;;! target = "x86_64"
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
;;    0: pushq   %rbp
;;    1: movq    %rsp, %rbp
;;    4: movl    %edx, %r9d
;;    7: cmpq    0x1a(%rip), %r9
;;    e: ja      0x25
;;   14: movq    0x50(%rdi), %r11
;;   18: movl    %ecx, 0x1000(%r11, %r9)
;;   20: movq    %rbp, %rsp
;;   23: popq    %rbp
;;   24: retq
;;   25: ud2
;;   27: addb    %bh, %ah
;;   29: outl    %eax, %dx
;;
;; wasm[0]::function[1]:
;;   30: pushq   %rbp
;;   31: movq    %rsp, %rbp
;;   34: movl    %edx, %r9d
;;   37: cmpq    0x1a(%rip), %r9
;;   3e: ja      0x55
;;   44: movq    0x50(%rdi), %r11
;;   48: movl    0x1000(%r11, %r9), %eax
;;   50: movq    %rbp, %rsp
;;   53: popq    %rbp
;;   54: retq
;;   55: ud2
;;   57: addb    %bh, %ah
;;   59: outl    %eax, %dx
