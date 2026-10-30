NVCC ?= nvcc
CUDA_TEST_BIN ?= /tmp/xark-msm-digits-test
BUCKET_TEST_BIN ?= /tmp/xark-msm-bucketize-test
HOST_TEST_BIN ?= /tmp/xark-msm-digits-host-test
BUCKET_HOST_TEST_BIN ?= /tmp/xark-msm-bucketize-host-test
FQ_HOST_TEST_BIN ?= /tmp/xark-msm-fq-host-probe
G1_HOST_TEST_BIN ?= /tmp/xark-msm-g1-host-probe
G1_CUDA_TEST_BIN ?= /tmp/xark-msm-g1-test
CXX ?= c++

.PHONY: test test-host clean

test: test-host
	$(NVCC) -std=c++17 -O3 -Xcompiler=-Wall,-Wextra,-Werror msm_digits_test.cu -o $(CUDA_TEST_BIN)
	$(CUDA_TEST_BIN)
	$(NVCC) -std=c++17 -O3 -Xcompiler=-Wall,-Wextra,-Werror msm_bucketize_test.cu -o $(BUCKET_TEST_BIN)
	$(BUCKET_TEST_BIN)
	$(NVCC) -std=c++17 -O3 -Xcompiler=-Wall,-Wextra,-Werror msm_g1_test.cu -o $(G1_CUDA_TEST_BIN)
	$(G1_CUDA_TEST_BIN)

test-host:
	$(CXX) -std=c++17 -O2 -Wall -Wextra -Werror msm_digits_host_test.cpp -o $(HOST_TEST_BIN)
	$(HOST_TEST_BIN)
	$(CXX) -std=c++17 -O2 -Wall -Wextra -Werror msm_bucketize_host_test.cpp -o $(BUCKET_HOST_TEST_BIN)
	$(BUCKET_HOST_TEST_BIN)
	$(CXX) -std=c++17 -O2 -Wall -Wextra -Werror msm_fq_host_probe.cpp -o $(FQ_HOST_TEST_BIN)
	python3 msm_fq_host_test.py $(FQ_HOST_TEST_BIN)
	$(CXX) -std=c++17 -O2 -Wall -Wextra -Werror msm_g1_host_probe.cpp -o $(G1_HOST_TEST_BIN)
	python3 msm_g1_host_test.py $(G1_HOST_TEST_BIN)

clean:
	rm -f $(CUDA_TEST_BIN) $(BUCKET_TEST_BIN) $(G1_CUDA_TEST_BIN) $(HOST_TEST_BIN) $(BUCKET_HOST_TEST_BIN) $(FQ_HOST_TEST_BIN) $(G1_HOST_TEST_BIN)
