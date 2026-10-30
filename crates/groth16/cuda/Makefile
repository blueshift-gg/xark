NVCC ?= nvcc
CUDA_TEST_BIN ?= /tmp/xark-msm-digits-test
BUCKET_TEST_BIN ?= /tmp/xark-msm-bucketize-test
HOST_TEST_BIN ?= /tmp/xark-msm-digits-host-test
CXX ?= c++

.PHONY: test test-host clean

test: test-host
	$(NVCC) -std=c++17 -O3 -Xcompiler=-Wall,-Wextra,-Werror msm_digits_test.cu -o $(CUDA_TEST_BIN)
	$(CUDA_TEST_BIN)
	$(NVCC) -std=c++17 -O3 -Xcompiler=-Wall,-Wextra,-Werror msm_bucketize_test.cu -o $(BUCKET_TEST_BIN)
	$(BUCKET_TEST_BIN)

test-host:
	$(CXX) -std=c++17 -O2 -Wall -Wextra -Werror msm_digits_host_test.cpp -o $(HOST_TEST_BIN)
	$(HOST_TEST_BIN)

clean:
	rm -f $(CUDA_TEST_BIN) $(BUCKET_TEST_BIN) $(HOST_TEST_BIN)
