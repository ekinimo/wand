#!/bin/bash

# Build the project first
echo "Building wand..."
cargo build --release

if [ $? -ne 0 ]; then
    echo "Build failed!"
    exit 1
fi

echo "Running e2e tests..."
echo "===================="

# Arrays to track errors
transpilation_errors=()
execution_errors=()
successful_tests=()

# Find all .wand files in e2e_tests directory
for test_file in e2e_tests/*.wand; do
    if [ -f "$test_file" ]; then
        test_name=$(basename "$test_file" .wand)
        echo "Testing: $test_name"
        echo "------------------------"
        
        # Read the test file content
        echo "Code:"
        cat "$test_file"
        echo
        
        # Try to transpile
        echo "Transpiling..."
        if ./target/release/wand --transpile "$test_file" > /dev/null 2>&1; then
            echo "✅ Transpilation successful"
            
            # Try to run the output
            echo "Running JavaScript output..."
            if node output.js > /dev/null 2>&1; then
                echo "✅ Execution successful"
                successful_tests+=("$test_name")
            else
                echo "❌ Execution failed"
                execution_errors+=("$test_name")
            fi
        else
            echo "❌ Transpilation failed"
            transpilation_errors+=("$test_name")
        fi
        
        echo
        echo "========================"
        echo
    fi
done

echo
echo "========================================="
echo "               SUMMARY"
echo "========================================="
echo

echo "✅ SUCCESSFUL TESTS (${#successful_tests[@]}):"
for test in "${successful_tests[@]}"; do
    echo "  $test"
done
echo

if [ ${#transpilation_errors[@]} -gt 0 ]; then
    echo "❌ TRANSPILATION ERRORS (${#transpilation_errors[@]}):"
    for error in "${transpilation_errors[@]}"; do
        echo "  $error"
    done
    echo
fi

if [ ${#execution_errors[@]} -gt 0 ]; then
    echo "❌ EXECUTION ERRORS (${#execution_errors[@]}):"
    for error in "${execution_errors[@]}"; do
        echo "  $error"
    done
    echo
fi

total_tests=$((${#successful_tests[@]} + ${#transpilation_errors[@]} + ${#execution_errors[@]}))
echo "TOTAL: $total_tests tests, ${#successful_tests[@]} successful, $((${#transpilation_errors[@]} + ${#execution_errors[@]})) failed"
