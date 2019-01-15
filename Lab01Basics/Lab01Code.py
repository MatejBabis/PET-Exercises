#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 01
#
# Basics of Petlib, encryption, signatures and
# an end-to-end encryption system.
#
# Run the tests through:
# $ py.test-2.7 -v Lab01Tests.py 

###########################
# Group Members: BABIS Matej, MOIRAS Stavros
###########################


#####################################################
# TASK 1 -- Ensure petlib is installed on the System
#           and also pytest. Ensure the Lab Code can 
#           be imported.

import petlib

#####################################################
# TASK 2 -- Symmetric encryption using AES-GCM 
#           (Galois Counter Mode)
#
# Implement a encryption and decryption function
# that simply performs AES_GCM symmetric encryption
# and decryption using the functions in petlib.cipher.

from os import urandom
from petlib.cipher import Cipher
from pytest import raises

aes = Cipher("aes-128-gcm")
iv = urandom(16)  # requires 16-bit IV


def encrypt_message(K, message):
   """ Encrypt a message under a key K """
   
   plaintext = message.encode("utf8")
   ciphertext, tag = aes.quick_gcm_enc(K, iv, plaintext)
   
   return iv, ciphertext, tag


def decrypt_message(K, iv, ciphertext, tag):
   """ Decrypt a cipher text under a key K

        In case the decryption fails, throw an exception.
    """
   with raises(Exception) as excinfo:
      plain = aes.quick_gcm_dec(K, iv, ciphertext, tag)
   assert 'decryption failed' in str(excinfo.value)
   
   return plain.encode("utf8")


#####################################################
# TASK 3 -- Understand Elliptic Curve Arithmetic
#           - Test if a point is on a curve.
#           - Implement Point addition.
#           - Implement Point doubling.
#           - Implement Scalar multiplication (double & add).
#           - Implement Scalar multiplication (Montgomery ladder).
#
# MUST NOT USE ANY OF THE petlib.ec FUNCTIONS. Only petlib.bn!

from petlib.bn import Bn


def is_point_on_curve(a, b, p, x, y):
   """
    Check that a point (x, y) is on the curve defined by a,b and prime p.
    Reminder: an Elliptic Curve on a prime field p is defined as:

              y^2 = x^3 + ax + b (mod p)
                  (Weierstrass form)

    Return True if point (x,y) is on curve, otherwise False.
    By convention a (None, None) point represents "infinity".
    """
   
   assert isinstance(a, Bn)
   assert isinstance(b, Bn)
   assert isinstance(p, Bn) and p > 0
   assert (isinstance(x, Bn) and isinstance(y, Bn)) or (x is None and y is None)
   
   if x is None and y is None:
      return True
   
   lhs = (y * y) % p
   rhs = (x * x * x + a * x + b) % p
   on_curve = (lhs == rhs)
   
   return on_curve


def point_add(a, b, p, x0, y0, x1, y1):
   """Define the "addition" operation for 2 EC Points.

    Reminder: (xr, yr) = (xq, yq) + (xp, yp)
    is defined as:
        lam = (yq - yp) * (xq - xp)^-1 (mod p)
        xr  = lam^2 - xp - xq (mod p)
        yr  = lam * (xp - xr) - yp (mod p)

    Return the point resulting from the addition. Raises an Exception if the points are equal.
    """
   
   # check if the points satisfy the curve equation
   if not is_point_on_curve(a, b, p, x0, y0) or not is_point_on_curve(a, b, p, x1, y1):
      raise Exception("One of the points not on curve")
   
   # if one of the elements is a neutral element (point at infinity),
   # return the result of the addition is the other point
   if x0 is None and y0 is None:
      return x1, y1
   if x1 is None and y1 is None:
      return x0, y0
   
   # special case: raise an exception, this is solved in doubling
   if (x0, y0) == (x1, y1):
      raise Exception("EC Points must not be equal")
   
   # result of adding two points with the same remainder is a neutral element
   if x0 % p == x1 % p or y0 % p == y1 % p:
      return None, None
      
   # operator syntax not available for inverses, so have to use a function,
   # otherwise use the formula
   lam = ((y1 - y0) * (x1 - x0).mod_inverse(p)) % p
   xr = (lam ** 2 - x0 - x1) % p
   yr = (lam * (x0 - xr) - y0) % p

   return xr, yr


def point_double(a, b, p, x, y):
   """Define "doubling" an EC point.
     A special case, when a point needs to be added to itself.

     Reminder:
        lam = (3 * xp ^ 2 + a) * (2 * yp) ^ -1 (mod p)
        xr  = lam ^ 2 - 2 * xp
        yr  = lam * (xp - xr) - yp (mod p)

    Returns the point representing the double of the input (x, y).
    """
   
   # check if the point satisfies the curve equation
   if not is_point_on_curve(a, b, p, x, y):
      raise Exception("Point not on curve")
   
   # if the point is a neutral element, the result is also a neutral element
   if x is None and y is None:
      return x, y

   # compute the value according to the formula
   lam = ((3 * x ** 2 + a) * (2 * y).mod_inverse(p)) % p
   xr = ((lam ** 2) - 2 * x) % p
   yr = (lam * (x - xr) - y) % p
   
   return xr, yr


def point_scalar_multiplication_double_and_add(a, b, p, x, y, scalar):
   """
    Implement Point multiplication with a scalar:
        r * (x, y) = (x, y) + ... + (x, y)    (r times)

    Reminder of Double and Multiply algorithm: r * P
        Q = infinity
        for i = 0 to num_bits(P)-1
            if bit i of r == 1 then
                Q = Q + P
            P = 2 * P
        return Q

    """

   # inverse string binary representation of a decimal number (low to high)
   def dec_to_inv_binstr(dec):
      return str(bin(dec)[2:])[::-1]
   
   if not is_point_on_curve(a, b, p, x, y):
      raise Exception("Point not on curve")
   
   Q = (None, None)
   P = (x, y)

   scalar_bin = dec_to_inv_binstr(scalar)
   for i in range(scalar.num_bits()):
      if scalar_bin[i] == "1":
         Q = point_add(a, b, p, Q[0], Q[1], P[0], P[1])

      P = point_double(a, b, p, P[0], P[1])
   
   return Q


def point_scalar_multiplication_montgomerry_ladder(a, b, p, x, y, scalar):
   """
    Implement Point multiplication with a scalar:
        r * (x, y) = (x, y) + ... + (x, y)    (r times)

    Reminder of Double and Multiply algorithm: r * P
        R0 = infinity
        R1 = P
        for i in num_bits(P)-1 to zero:
            if di = 0:
                R1 = R0 + R1
                R0 = 2R0
            else
                R0 = R0 + R1
                R1 = 2R1
        return R0

    """
   # string binary representation of a decimal number (high to low)
   def dec_to_binstr(dec):
      return str(bin(dec)[2:])
   
   if not is_point_on_curve(a, b, p, x, y):
      raise Exception("Point not on curve")
   
   R0 = (None, None)
   R1 = (x, y)

   scalar_bin = dec_to_binstr(scalar)
   for i in range(scalar.num_bits()):
      # computes the point multiplication in a fixed amount of time
      # to prevent timing/power side-channel attacks
      if scalar_bin[i] == "0":
         R1 = point_add(a, b, p, R0[0], R0[1], R1[0], R1[1])
         R0 = point_double(a, b, p, R0[0], R0[1])
      else:
         R0 = point_add(a, b, p, R0[0], R0[1], R1[0], R1[1])
         R1 = point_double(a, b, p, R1[0], R1[1])
   
   return R0


#####################################################
# TASK 4 -- Standard ECDSA signatures
#
#          - Implement a key / param generation 
#          - Implement ECDSA signature using petlib.ecdsa
#          - Implement ECDSA signature verification 
#            using petlib.ecdsa

from hashlib import sha256
from petlib.ec import EcGroup
from petlib.ecdsa import do_ecdsa_sign, do_ecdsa_verify

def ecdsa_key_gen():
   """ Returns an EC group, a random private key for signing
        and the corresponding public key for verification"""
   G = EcGroup()
   priv_sign = G.order().random()
   pub_verify = priv_sign * G.generator()
   return G, priv_sign, pub_verify


def ecdsa_sign(G, priv_sign, message):
   """ Sign the SHA256 digest of the message using ECDSA and return a signature """
   plaintext = message.encode("utf8")

   digest = sha256(plaintext).digest()
   sig = do_ecdsa_sign(G, priv_sign, digest)

   return sig


def ecdsa_verify(G, pub_verify, message, sig):
   """ Verify the ECDSA signature on the message """
   plaintext = message.encode("utf8")

   digest = sha256(plaintext).digest()
   res = do_ecdsa_verify(G, pub_verify, sig, digest)
   
   return res


#####################################################
# TASK 5 -- Diffie-Hellman Key Exchange and Derivation
#           - use Bob's public key to derive a shared key.
#           - Use Bob's public key to encrypt a message.
#           - Use Bob's private key to decrypt the message.
#
# NOTE: 

def dh_get_key():
   """ Generate a DH key pair """
   G = EcGroup()
   priv_dec = G.order().random()
   pub_enc = priv_dec * G.generator()
   return (G, priv_dec, pub_enc)


def dh_encrypt(pub, message, aliceSig=None):
   """ Assume you know the public key of someone else (Bob),
    and wish to Encrypt a message for them.
        - Generate a fresh DH key for this message.
        - Derive a fresh shared key.
        - Use the shared key to AES_GCM encrypt the message.
        - Optionally: sign the message with Alice's key.
    """

   G, priv_dec, pub_enc = dh_get_key()
   


def dh_decrypt(priv, ciphertext, aliceVer=None):
   """ Decrypt a received message encrypted using your public key,
    of which the private key is provided. Optionally verify 
    the message came from Alice using her verification key."""
   
   ## YOUR CODE HERE
   pass


## NOTE: populate those (or more) tests
#  ensure they run using the "py.test filename" command.
#  What is your test coverage? Where is it missing cases?
#  $ py.test-2.7 --cov-report html --cov Lab01Code Lab01Code.py 

def test_encrypt():
   assert False


def test_decrypt():
   assert False


def test_fails():
   assert False


#####################################################
# TASK 6 -- Time EC scalar multiplication
#             Open Task.
#           
#           - Time your implementations of scalar multiplication
#             (use time.clock() for measurements)for different 
#              scalar sizes)
#           - Print reports on timing dependencies on secrets.
#           - Fix one implementation to not leak information.

def time_scalar_mul():
   pass
