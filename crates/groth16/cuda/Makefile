NVCC ?= nvcc
CUDA_TEST_BIN ?= /tmp/xark-msm-digits-test

.PHONY: test clean

test:
	$(NVCC) -std=c++17 -O3 -Xcompiler=-Wall,-Wextra,-Werror msm_digits_test.cu -o $(CUDA_TEST_BIN)
	$(CUDA_TEST_BIN)

clean:
	rm -f $(CUDA_TEST_BIN)
