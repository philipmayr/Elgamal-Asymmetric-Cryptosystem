// Implementation of Elgamal Cryptosystem

#include <time.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

typedef uint64_t integer;

const double EXPONENTIAL_CONSTANT = 2.718281828459045235357;

integer draw_random_integer(integer exclusive_lower_bound, integer exclusive_upper_bound)
{
    return rand() % (exclusive_upper_bound - exclusive_lower_bound + 1) + exclusive_lower_bound;
}

integer find_greatest_common_divisor(integer a, integer b)
{
    return b ? find_greatest_common_divisor(b, a % b) : a;
}

integer find_totient(integer number)
{
    integer totient = 1;
    
    for (integer index = 2; index < number; index++)
        if (find_greatest_common_divisor(index, number) == 1)
            totient++;
            
    return totient;
}

integer depotentiate_binarily(integer number)
{
    integer exponent = 1;
    
    while (number >>= 1) exponent++;
    
    return exponent;
}

double depotentiate_by_exponential_constant(double number)
{
    double inverse_of_binary_depotentiation_of_exponential_constant = 1.0 / depotentiate_binarily(EXPONENTIAL_CONSTANT);
    
    double natural_depotentiation = depotentiate_binarily(number) * inverse_of_binary_depotentiation_of_exponential_constant;
    
    return natural_depotentiation;
}

double find_square_root(double square)
{
    double x = square;
    double y = 1;
    
    double epsilon = 0.000001;
    
    while ((x - y) > epsilon)
    {
        x = (x + y) / 2;
        y = square / x;
    }
    
    return x;
}

integer * find_distinct_prime_factors(integer number, integer * upper_bound)
{
    integer * distinct_prime_factors = malloc(sizeof (integer) * * upper_bound);
    
    integer index = 0;
    
    if (~number & 1)
    {
        distinct_prime_factors[index] = 2;
        
        index++;
        
        do number >>= 1; while (~number & 1);
    }
    
    for (integer factor_candidate = 3; factor_candidate <= find_square_root(number); factor_candidate += 2)
    {
        if (number % factor_candidate == 0) 
        {
            integer factor = factor_candidate;
            
            distinct_prime_factors[index] = factor;
            
            index++;
            
            do number /= factor; while (number % factor == 0);
        }
    }
    
    if (number > 2)
    {
        distinct_prime_factors[index] = number;
    
        index++;
    }
    
    * upper_bound = index;
    
    return distinct_prime_factors;
}

integer * find_prime_factors(integer number, integer * upper_bound)
{
    integer * prime_factors = malloc(sizeof (int) * * upper_bound);
    
    integer index = 0;
    
    while (~number & 1)
    {
        prime_factors[index] = 2;
        
        number >>= 1;
        
        index++;
    }
    
    for (integer factor_candidate = 3; factor_candidate <= find_square_root(number); factor_candidate += 2)
    {
        while (number % factor_candidate == 0)
        {
            integer factor = factor_candidate;
            
            prime_factors[index] = factor;
            
            number /= factor;
            
            index++;
        }
    }
    
    if (number > 2) prime_factors[index] = number;
    
    * upper_bound = index;
    
    return prime_factors;
}

integer exponentiate(integer base, integer index)
{
    if (base == 0) return 0;
    if (index == 0) return 1;
    if (index == 1) return base;

    integer power = 1;
    
    while (index)
    {
        power *= power * exponentiate(base, index & 1);
        index >>= 1;
    }
    
    return power;    
}

integer exponentiate_modularly(integer base, integer index, integer modulus)
{
    if (base == 0) return 0;
    if (index == 0) return 1;

    if (base > modulus) base %= modulus;
    if (index == 1) return base;
    
    integer residue = 1;
            
    while (index)
    {
        if (index & 1) residue = (residue * base) % modulus;
        
        base = (base * base) % modulus;
        index >>= 1;
    }
    
    return residue;    
}

// Miller-Rabin Primality Test

integer test_primality(integer prime_candidate, integer rounds)
{
    if (prime_candidate == 2) return 1;
    if (~prime_candidate & 1 || prime_candidate < 2) return 0;
    
    integer greatest_power_of_two_factor_of_prime_candidate_less_one = 1;
    const integer prime_candidate_less_one = prime_candidate - 1;

    while (prime_candidate_less_one % exponentiate(2, greatest_power_of_two_factor_of_prime_candidate_less_one) == 0) 
        greatest_power_of_two_factor_of_prime_candidate_less_one++;

    greatest_power_of_two_factor_of_prime_candidate_less_one--;
    
    const integer multiplier = prime_candidate_less_one / exponentiate(2, greatest_power_of_two_factor_of_prime_candidate_less_one);
    
    for (integer round = 1; round < rounds; round++)
    {
        // get random base
        integer base = draw_random_integer(1, prime_candidate_less_one);
        const integer greatest_common_divisor = find_greatest_common_divisor(base, prime_candidate);
        
        if (greatest_common_divisor > 1 && greatest_common_divisor < prime_candidate) return 0;
    
        base = exponentiate_modularly(base, multiplier, prime_candidate);
        
        if (base != 1 && base != prime_candidate_less_one)
        {
            for (integer index = 1; index < greatest_power_of_two_factor_of_prime_candidate_less_one && base != prime_candidate_less_one; index++)
            {
                base = exponentiate_modularly(base, 2, prime_candidate);
                
                if (base == 1) return 0;
            }
            
            if (base != prime_candidate_less_one) return 0;
        }
    }
    
    return 1;
}

integer draw_random_prime_number(integer bit_length)
{
    for (;;)
    {
        integer random_integer = draw_random_integer(0, (1 << bit_length) + 1);
        
        const integer bit_mask = (1 << (bit_length - 1)) | 1;
        
        random_integer |= bit_mask;
        
        if (test_primality(random_integer, 2)) return random_integer;
    }
}

integer find_least_primitive_root(integer prime_number)
{
    if (prime_number == 2) return 1;
    
    // primitive root α
    integer primitive_root = 2;
    
    integer prime_number_less_one = prime_number - 1;
    
    // number of primitive roots of n is equal to phi(phi(n))
    integer number_of_primitive_roots = find_totient(find_totient(prime_number));
    
    integer * primitive_roots = malloc(sizeof (int) * number_of_primitive_roots);
    
    integer upper_bound = depotentiate_by_exponential_constant(prime_number) / depotentiate_by_exponential_constant(depotentiate_by_exponential_constant(prime_number_less_one));
        
    integer * distinct_prime_factors = find_distinct_prime_factors(prime_number_less_one, & upper_bound);
    
    iterate_over_distinct_prime_factors:
    for (integer index = 0; index < upper_bound; index++)
    {
        integer exponent = (prime_number_less_one) / (* (distinct_prime_factors + index));
        
        if (exponentiate_modularly(primitive_root, exponent, prime_number) == 1)
        {
            primitive_root++;
            goto iterate_over_distinct_prime_factors;
        }
        else if (index == number_of_primitive_roots - 1)
            return primitive_root;
    }
    
    return primitive_root;
}

integer find_modular_multiplicative_inverse(integer multiplicand, integer modulus)
{
    if (find_greatest_common_divisor(multiplicand, modulus) != 1)
        return -1;
    
    integer modular_multiplicative_inverse_candidate = 0;
    
    while ((multiplicand * modular_multiplicative_inverse_candidate % modulus != 1) && modular_multiplicative_inverse_candidate < modulus)
        modular_multiplicative_inverse_candidate++;
    
    integer modular_multiplicative_inverse = modular_multiplicative_inverse_candidate;

    return modular_multiplicative_inverse;
}

integer get_padding(integer number)
{
    if (number < 10)
        return 4;
    else if (number < 100)
        return 3;
    else if (number < 1000)
        return 2;
    else if (number < 10000)
        return 1;
    else
        return 0;
}

integer main()
{
    srand(time(NULL));

    const integer bit_length = 16;
    
    // set domain parameters
    const integer public_prime_modulus = draw_random_prime_number(bit_length);
    integer public_primitive_root = find_least_primitive_root(public_prime_modulus); // generator

    // transmitter
    const integer transmitter_private_exponent_key = draw_random_integer(1, public_prime_modulus - 1);
    const integer transmitter_public_power = exponentiate_modularly(public_primitive_root, transmitter_private_exponent_key, public_prime_modulus);
        // -> transmitter sends resulting power to receiver in the clear
    
    // receiver
    const integer receiver_private_exponent_key = draw_random_integer(1, public_prime_modulus - 1);
    const integer receiver_public_power = exponentiate_modularly(public_primitive_root, receiver_private_exponent_key, public_prime_modulus);
        // -> receiver sends resulting power to transmitter in the clear
        
    // transmitter
    const integer transmitter_copy_shared_secret_key = exponentiate_modularly(receiver_public_power, transmitter_private_exponent_key, public_prime_modulus);
    
    // receiver
    const integer receiver_copy_shared_secret_key = exponentiate_modularly(transmitter_public_power, receiver_private_exponent_key, public_prime_modulus);
    
    printf("Transmitter's copy of shared secret key: %ld", transmitter_copy_shared_secret_key);
    printf("\n");
    printf("Receiver's copy of shared secret key:    %ld", receiver_copy_shared_secret_key);
    
    printf("\n\n");

    const integer message = draw_random_integer(1, public_prime_modulus - 1);
    
    integer spaces = get_padding(message);
        
    printf("Clear (uncrypted) message:  ");
    
    for (integer iteration = 0; iteration < spaces; iteration++) printf(" ");
    
    printf("%ld", message);
    
    printf("\n");

    const integer secret_message = (message * receiver_copy_shared_secret_key) % public_prime_modulus;
    
    spaces = get_padding(secret_message);
        
    printf("Secret (encrypted) message: ");
        
    for (integer iteration = 0; iteration < spaces; iteration++) printf(" ");
    
    printf("%ld", secret_message);
    
    printf("\n");
    
    const integer shared_secret_inverse = find_modular_multiplicative_inverse(receiver_copy_shared_secret_key, public_prime_modulus);
    
    const integer decrypted_secret_message = shared_secret_inverse * secret_message % public_prime_modulus;
    
    spaces = get_padding(decrypted_secret_message);
        
    printf("Clear (decrypted) message:  ");
    
    for (integer iteration = 0; iteration < spaces; iteration++) printf(" ");
    
    printf("%ld", decrypted_secret_message);

    return 0;
}
