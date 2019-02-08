#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 03
#
# Basics of Privacy Friendly Computations through
#         Additive Homomorphic Encryption.
#
# Run the tests through:
# $ py.test -v test_file_name.py

#####################################################
# TASK 1 -- Setup, key derivation, log
#           Encryption and Decryption
#

###########################
# Group Members: TODO
###########################


from petlib.ec import EcGroup


def setup():
    """Generates the Cryptosystem Parameters."""
    G = EcGroup(nid=713)
    g = G.hash_to_point(b"g")
    h = G.hash_to_point(b"h")
    o = G.order()
    return G, g, h, o


def keyGen(params):
   """ Generate a private / public key pair """
   (G, g, h, o) = params
   
   priv = G.order().random()
   pub = priv * g
   
   return priv, pub


def encrypt(params, pub, m):
    """ Encrypt a message under the public key """
    if not -100 < m < 100:
        raise Exception("Message value to low or high.")

    (G, g, h, o) = params
    k = G.order().random()      # random number mod the order of the group
    
    a = k * g                   # g^k
    b = k * pub + m * h         # g^xk h^m

    # return ciphertext pair
    return a, b


def isCiphertext(params, ciphertext):
    """ Check a ciphertext """
    (G, g, h, o) = params
    ret = len(ciphertext) == 2
    a, b = ciphertext
    ret &= G.check_point(a)
    ret &= G.check_point(b)
    return ret


_logh = None
def logh(params, hm):
    """ Compute a discrete log, for small number only """
    global _logh
    (G, g, h, o) = params

    # Initialize the map of logh
    if _logh == None:
        _logh = {}
        for m in range (-1000, 1000):
            _logh[(m * h)] = m

    if hm not in _logh:
        raise Exception("No decryption found.")

    return _logh[hm]


def decrypt(params, priv, ciphertext):
    """ Decrypt a message using the private key """
    assert isCiphertext(params, ciphertext)

    a, b = ciphertext

    hm = b - priv * a       # inner part of the log: b * (a^x)^(-1)

    return logh(params, hm)


#####################################################
# TASK 2 -- Define homomorphic addition and
#           multiplication with a public value
#

def add(params, pub, c1, c2):
    """ Given two ciphertexts compute the ciphertext of the 
        sum of their plaintexts.
    """
    assert isCiphertext(params, c1)
    assert isCiphertext(params, c2)

    a1, b1 = c1
    a2, b2 = c2
    
    # E(m1 + m2, k1 + k2) = (a1a2, b1b2)
    return a1 + a2, b1 + b2


def mul(params, pub, c1, alpha):
    """ Given a ciphertext compute the ciphertext of the 
        product of the plaintext time alpha """
    assert isCiphertext(params, c1)

    a1, b1 = c1

    # E(cm1, ck1) = (a1^c, b1^c)
    return alpha * a1, alpha * b1


#####################################################
# TASK 3 -- Define Group key derivation & Threshold
#           decryption. Assume an honest but curious 
#           set of authorities.

def groupKey(params, pubKeys=[]):
    """ Generate a group public key from a list of public keys """
    
    assert(len(pubKeys) > 0)    # sanity check
    
    # pk = g^(x1+...xn)
    pub = pubKeys[0]
    for pk in pubKeys[1:]:
        pub += pk

    return pub


def partialDecrypt(params, priv, ciphertext, final=False):
    """ Given a ciphertext and a private key, perform partial decryption. 
        If final is True, then return the plaintext. """
    assert isCiphertext(params, ciphertext)
    
    a1, b = ciphertext      # a1 == a
    b1 = b - priv * a1      # intermediate step: b * (a^x)^(-1)

    if final:
        return logh(params, b1)
    else:
        return a1, b1


#####################################################
# TASK 4 -- Actively corrupt final authority, derives
#           a public key with a known private key.
#

def corruptPubKey(params, priv, OtherPubKeys=[]):
    """ Simulate the operation of a corrupt decryption authority. 
        Given a set of public keys from other authorities return a
        public key for the corrupt authority that leads to a group
        public key corresponding to a private key known to the
        corrupt authority. """
    (G, g, h, o) = params

    assert (len(OtherPubKeys) > 0)  # sanity check

    # derive the public key of the malicious authority
    malicious_pub = priv * g
    # compute the legitimate public key
    legit_pub = groupKey(params, OtherPubKeys)

    # return corrupt public key: malicious_pk / product of legitimate_pks
    return malicious_pub - legit_pub


#####################################################
# TASK 5 -- Implement operations to support a simple
#           private poll.
#

def encode_vote(params, pub, vote):
    """ Given a vote 0 or 1 encode the vote as two
        ciphertexts representing the count of votes for
        zero and the votes for one."""
    assert vote in [0, 1]

    # if the vote is 0, have v0 = 1 (and v1 = 0)
    # do the opposite for when vote is 1
    v0 = encrypt(params, pub, 1-vote)
    v1 = encrypt(params, pub, vote)

    return v0, v1


def process_votes(params, pub, encrypted_votes):
    """ Given a list of encrypted votes tally them
        to sum votes for zeros and votes for ones. """
    assert isinstance(encrypted_votes, list)
    assert (len(encrypted_votes) > 0)  # sanity check
    
    # starting value
    total_v0, total_v1 = encrypted_votes[0]
    # accumulate total for each vote (without decrypting)
    for v0, v1 in encrypted_votes[1:]:
        total_v0 = add(params, pub, v0, total_v0)
        total_v1 = add(params, pub, v1, total_v1)

    return total_v0, total_v1


def simulate_poll(votes):
    """ Simulates the full process of encrypting votes,
        tallying them, and then decrypting the total. """

    # Generate parameters for the crypto-system
    params = setup()

    # Make keys for 3 authorities
    priv1, pub1 = keyGen(params)
    priv2, pub2 = keyGen(params)
    priv3, pub3 = keyGen(params)
    pub = groupKey(params, [pub1, pub2, pub3])

    # Simulate encrypting votes
    encrypted_votes = []
    for v in votes:
        encrypted_votes.append(encode_vote(params, pub, v))

    # Tally the votes
    total_v0, total_v1 = process_votes(params, pub, encrypted_votes)

    # Simulate threshold decryption
    privs = [priv1, priv2, priv3]
    for priv in privs[:-1]:
        total_v0 = partialDecrypt(params, priv, total_v0)
        total_v1 = partialDecrypt(params, priv, total_v1)

    total_v0 = partialDecrypt(params, privs[-1], total_v0, True)
    total_v1 = partialDecrypt(params, privs[-1], total_v1, True)

    # Return the plaintext values
    return total_v0, total_v1

###########################################################
# TASK Q1 -- Answer questions regarding your implementation
#
# Consider the following game between an adversary A and honest users H1 and H2: 
# 1) H1 picks 3 plaintext integers Pa, Pb, Pc arbitrarily, and encrypts them to the public
#    key of H2 using the scheme you defined in TASK 1.
# 2) H1 provides the ciphertexts Ca, Cb and Cc to H2 who flips a fair coin b.
#    In case b=0 then H2 homomorphically computes C as the encryption of Pa plus Pb.
#    In case b=1 then H2 homomorphically computes C as the encryption of Pb plus Pc.
# 3) H2 provides the adversary A, with Ca, Cb, Cc and C.
#
# What is the advantage of the adversary in guessing b given your implementation of 
# Homomorphic addition? What are the security implications of this?

"""
Homomorphic schemes are not CCA-secure.

Should the adversary have access to a decryption oracle, it would be able
to determine the value of b using addition of ciphertext combinations,
encryption of the results and comparison with the ciphertexts received from H2.

Additional security measures should be considered to prevent this,
for instance using zero-knowledge proofs.
"""

###########################################################
# TASK Q2 -- Answer questions regarding your implementation
#
# Given your implementation of the private poll in TASK 5, how
# would a malicious user implement encode_vote to (a) distrupt the
# poll so that it yields no result, or (b) manipulate the poll so 
# that it yields an arbitrary result. Can those malicious actions 
# be detected given your implementation?

"""
The idea behind private polling is knowing the sum of all the votes,
without being able to tell what an individual voted for.

An adversary can use this to their advantage by implementing an encoding
function that uses arbitrarily large (positive OR negative) values to skew
the results based on their preferences.
"""