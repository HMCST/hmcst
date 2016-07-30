#define MAX_THREADS (3)
#define NONE (255)
#define UNLOCKED (true)
#define WAIT (254)
#define ABANDONED (253)
#define RECYCLED (252)
#define IMPATIENT (254)
#define VALID_SUCC(id) (next[id] > 0  && next[id] < MAX_THREADS)
#define MY_STATUS status[myid]
#define MY_NEXT next[myid]

byte next[MAX_THREADS];
byte status[MAX_THREADS];
byte L;
byte inCS;
byte done = 0;
byte numAcquisitions;

#define SWAP(loc, var, val) d_step{var=loc; loc=val;}

#define CAS(loc, oldVal, newVal, retOld) d_step{ \
                          if \
                          :: loc == oldVal -> retOld = loc; loc = newVal;\
                          :: else -> retOld = loc;\
                          fi\
                        }

#define BOOL_CAS(loc, oldVal, newVal, retOld) d_step{ \
                          if \
                          :: loc == oldVal -> retOld = true; loc = newVal;\
                          :: else -> retOld = false;\
                          fi \
                        }


inline Acquire(abandonedNode, myid) {
    byte prevStatus;
    byte pred;
    byte predStat;
    byte tmpStatus;
        
    // Start with a swap
    SWAP(MY_STATUS, prevStatus, WAIT);
    if
    :: prevStatus == ABANDONED -> goto START_SPIN; // Reentry after abandonment
    :: d_step {prevStatus == RECYCLED -> skip;};  // Ready to enqueue
    :: d_step {prevStatus == WAIT -> skip;};    // Never happens
    :: prevStatus == UNLOCKED ->                 
        /*while(I->status != RECYCLED); No unbounded wait*/
       CAS(MY_STATUS, WAIT, UNLOCKED, tmpStatus);    // I had abandoned and the pred steped over me, wait till RECYCLED
       if
       :: d_step {tmpStatus != RECYCLED -> abandonedNode = myid;}; goto DONE_ACQUIRE; // Leaving due to timeout
       :: d_step {else -> skip; };  // Follow normal enqueue process
       fi
       :: d_step {else -> assert (false);}; // never happens
    fi
    USE_QNODE:
        // Init next field
        MY_NEXT = NONE;
        // swap tail pointer
        SWAP(L,pred, myid);
        if
        :: d_step {pred != NONE -> 
            // Have a predecessor, swap my id with pred->next
            SWAP(next[pred], predStat, myid);};
            if
            :: d_step {predStat == IMPATIENT -> // Pred had already left having become impatient, recycle pred
                status[pred]= RECYCLED;}; 
                goto SET_AND_FINISH_ACQUIRE; // Lock is mine
            :: else -> skip;
            fi
    START_SPIN:
            if
            :: d_step {MY_STATUS == UNLOCKED -> abandonedNode = NONE;};  // Got the lock from pred!
            :: else -> 
            	SWAP(MY_STATUS, prevStatus , ABANDONED); // Timed out waiting
                if
                :: d_step {prevStatus == UNLOCKED -> MY_STATUS = UNLOCKED; abandonedNode = NONE; }; // Got the lock, just in time!
                :: d_step {else -> abandonedNode = myid;} // Leaving due to timeout
                fi
            fi
            goto DONE_ACQUIRE;
        :: else -> goto SET_AND_FINISH_ACQUIRE; // No predecessor ==> I own the lock 
    fi


SET_AND_FINISH_ACQUIRE: skip;
d_step {
    MY_STATUS = UNLOCKED; // I am the lock owner, hence set status to UNLOCKED
    abandonedNode = NONE; 
}
DONE_ACQUIRE: skip;
}

inline AcquireWrapper(acquired, myid) {
    byte abandonedNode;
    Acquire(abandonedNode, myid);
    if
    :: d_step { abandonedNode==NONE ->  // Acquired! 
       acquired=true;  
       inCS++;     
       numAcquisitions++;
       };
       d_step{
       assert(inCS == 1);  // assert no one else in CS.
       inCS--;
       };
    :: d_step {else -> acquired=false;}; // Abandoned!
    fi
}


inline AttemptToRelinquishTheRootLevelLock(me, prev){
    byte tmpStatus;
    byte retOld;
    byte tmpSucc;
    do
    ::d_step { else ->
      // Attempt to set L to NONE
      BOOL_CAS(L, me, NONE, retOld);};        
      if 
      :: d_step {retOld == false -> 
         // Failed to set L to NONE, I have a successore
         // Can't wait for next to be updated, attempt to set IMPATIENT
         BOOL_CAS(next[me], NONE, IMPATIENT, retOld); };
         if 
         :: d_step { retOld == false ->
            // next got updated just in time
            // Try to UNLOCK the successor
            SWAP(status[next[me]], tmpStatus, UNLOCKED);};
            if
            ::  d_step { tmpStatus == ABANDONED ->
               // Successor already abandoned!
               // Keep looking
               tmpSucc = next[me];};
               d_step { next[me] = prev;
               prev = me;
               me =     tmpSucc;
               };
            ::  d_step {else -> status[me] = RECYCLED;}; break; // Gosh! passed the lock, recycle me.
            fi    
         :: else -> break;
         fi
       ::  d_step {else -> status[me] = RECYCLED;}; break; // Passed the lock, hence recycle the last node.
       fi
     od
}

inline Release(myid) {
    byte prev = NONE;
    byte me = myid;
    byte succ;
    byte pprev;
    byte prevStatus;

    do
    :: else ->
       if
       :: VALID_SUCC(me) -> 
          // There is a successor, try to pass the lock
          SWAP(status[next[me]], prevStatus , UNLOCKED);
          if
          ::  d_step {prevStatus == ABANDONED -> // Successor has abandoned! Keep looking for an unabandoned successor
              succ = next[me];    
              next[me] = prev;
              prev = me;
              me = succ; 
              }
          ::  d_step {else -> status[me] = RECYCLED;};  goto CLEANUP; // Lock passed, Recycle the last node.
          fi 
       :: else -> 
          AttemptToRelinquishTheRootLevelLock(me, prev); // No successor. Attempt to set the lock to NONE.
          goto CLEANUP;
       fi
    od
CLEANUP:
   // Recycle all nodes on which we had stepped
    do
    :: d_step{prev != NONE ->
        pprev = next[prev];};
        d_step{
        status[prev] = RECYCLED;
        prev = pprev;
        };
    :: else -> break;
    od
}


proctype  Work(byte myid) { 
    byte numRounds = 1;
    bool acquired;
    do
    :: numRounds > 0 -> 
       AcquireWrapper(acquired, myid); 
       if
       :: acquired -> Release(myid);
       :: else -> skip;
       fi
       numRounds--;
    :: else -> break;
    od;    
    done++;
}
 
proctype  WorkObserved(byte myid) { 
    byte numRounds = 2;
    bool acquired;
    do
    :: numRounds > 0 -> 
       AcquireWrapper(acquired, myid); 
       if
       :: acquired -> Release(myid);
       :: else -> skip;
       fi
       numRounds--;
    :: else -> break;
    od;    
    done++;
}
 
init {
     byte i;
     /* init */
         d_step{
         inCS = 0;
         L = NONE;
         for(i: 0..(MAX_THREADS-1)){
            next[i] = NONE;
            status[i] = RECYCLED;
         }
     }

    // 1 round for 2 participants
    run Work(/* my id*/ 0);
    run Work(/* my id*/ 1);
    // 2 rounds for 1 participant
    run WorkObserved(/* my id*/ 2);
    // Until all are done
    done == 3;
    // At least one acquisition should have happened.    
    assert(numAcquisitions >= 1);
    // All status fields must be in RECYCLED state.
    for(i: 0..(MAX_THREADS-1)){
        assert(status[i] == RECYCLED);
    }
} 

