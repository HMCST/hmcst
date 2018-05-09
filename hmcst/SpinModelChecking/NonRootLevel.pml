#define MAX_L1_THREADS (2)
#define MAX_L2_THREADS (3)
#define MAX_L3_THREADS (0)
#define THRESHOLD (2)
#define NONE (255)
#define UNLOCKED (true)
#define WAIT (254)
#define ABANDONED (253)
#define RECYCLED (252)
#define ACQUIRE_PARENT (250)
#define IMPATIENT (251)
#define COHORT_START (1)
#define MY_L1_STATUS statusL1[myL1Id]
#define MY_L1_NEXT nextL1[myL1Id]
#define L1_STATUS(id_1) statusL1[id_1]
#define L1_NEXT(id_2) nextL1[id_2]
#define HAS_VALID_L1_SUCC(id_3) nextL1[id_3] < MAX_L1_THREADS
#define MY_L2_STATUS statusL2[myL2Id]
#define MY_L2_NEXT nextL2[myL2Id]
#define L2_STATUS(id_4) statusL2[id_4]
#define L2_NEXT(id_5) nextL2[id_5]
#define HAS_VALID_L2_SUCC(id_6) nextL2[id_6] < MAX_L2_THREADS
#define MY_L1_NODE_ID(id) (id < MAX_L1_THREADS -> id : NONE)
#define MY_L2_NODE_ID(id) (id < MAX_L1_THREADS -> 0 : (id < (MAX_L1_THREADS + MAX_L2_THREADS - 1) -> id - (MAX_L1_THREADS- 1) : NONE) )
#define MY_L3_NODE_ID(id) (id < (MAX_L1_THREADS + MAX_L2_THREADS) -> 0 : NONE)


#define SWAP(loc_SWAP, var_SWAP, val_SWAP) d_step{var_SWAP=loc_SWAP; loc_SWAP=val_SWAP;}
#define CAS(loc_CAS, oldVal_CAS, newVal_CAS, retOld_CAS) d_step{ \
                          if \
                            :: loc_CAS == oldVal_CAS -> retOld_CAS = loc_CAS; loc_CAS = newVal_CAS;\
                            :: else -> retOld_CAS = loc_CAS;\
                          fi\
                        }
#define BOOL_CAS(loc_BCAS, oldVal_BCAS, newVal_BCAS, retOld_BCAS) d_step{ \
                          if \
                            :: loc_BCAS == oldVal_BCAS -> retOld_BCAS = true; loc_BCAS = newVal_BCAS;\
                            :: else -> retOld_BCAS = false;\
                          fi \
                        }

byte inCS=0;
byte inCSL1=0;
byte totalAcquisitions=0;
byte done=0;
byte nextL1[MAX_L1_THREADS];
byte statusL1[MAX_L1_THREADS];
byte L1;
byte nextL2[MAX_L2_THREADS];
byte statusL2[MAX_L2_THREADS];
byte L2;

inline AcquireL3(abortedLevel_Acq_L3) {
    /* non-deterministic acquire / abort here */
    if
    :: true -> d_step{
       abortedLevel_Acq_L3 = NONE; 
       inCS++; };
    :: true -> d_step{
       abortedLevel_Acq_L3 = 2; 
       inCS++; };
    fi;
    d_step{ assert(inCS == 1); 
    totalAcquisitions++;
    inCS--;};
}

inline AcquireL2(abortedLevel_Acq_L2, waiter_AW_L2) {
    byte prevStatus_Acq_L2;
    byte pred_Acq_L2;
    byte predNext_Acq_L2;
    byte tmpStatus_Acq_L2;
    SWAP(MY_L2_STATUS, prevStatus_Acq_L2, WAIT);
    atomic{
      if
      :: prevStatus_Acq_L2 == ABANDONED -> goto START_SPIN_L2; // Reentry after abandonment
      :: prevStatus_Acq_L2 == COHORT_START -> goto GOT_LOCK_L2; // This level was acquired by the thread that passed a prefix of locks to me
      :: prevStatus_Acq_L2 == WAIT -> MY_L2_NEXT = NONE; goto USE_QNODE_L2;  // Never happens
      :: prevStatus_Acq_L2 == RECYCLED -> MY_L2_NEXT = NONE; goto USE_QNODE_L2;  // Ready to enqueue
      :: else -> // This lock was abandoned and the pred steped over me, wait till RECYCLED
         /*while(I->status != RECYCLED); No unbounded wait*/
         if
         :: waiter_AW_L2 == true -> MY_L2_STATUS == RECYCLED; tmpStatus_Acq_L2=RECYCLED;
         :: waiter_AW_L2 == false -> CAS(MY_L2_STATUS, WAIT, ACQUIRE_PARENT, tmpStatus_Acq_L2);
         fi;

         //CAS(MY_L2_STATUS, WAIT, ACQUIRE_PARENT, tmpStatus_Acq_L2); // Timedout
         if
         :: tmpStatus_Acq_L2 != RECYCLED -> abortedLevel_Acq_L2 = 1 /* L2 */;  // Leaving due to timeout
            goto DONE_ACQUIRE_L2;
         :: else -> skip;  // Follow normal enqueue process
         fi
      fi
    };
    /** Happens only from else ***/
    // Init next field
    MY_L2_NEXT = NONE;

USE_QNODE_L2: skip;

    // swap tail pointer
    SWAP(L2,pred_Acq_L2, myL2Id);

    if
    :: atomic{ pred_Acq_L2 == NONE -> // No predecessor
GOT_LOCK_L2:
       MY_L2_STATUS = COHORT_START; /* lock is mine */ };
       AcquireL3(abortedLevel_Acq_L2); // Proceed to L3
    :: else ->
       // Have a predecessor, swap my id with pred->next
       SWAP(L2_NEXT(pred_Acq_L2), predNext_Acq_L2, myL2Id);
       if
       :: d_step { predNext_Acq_L2 == IMPATIENT -> // Pred had already left having become impatient, recycle pred
          L2_STATUS(pred_Acq_L2)= RECYCLED;};
          MY_L2_STATUS = COHORT_START; // Lock is mine, proceed to L3
          AcquireL3(abortedLevel_Acq_L2);
       :: else ->
START_SPIN_L2: skip;

          if 
          ::waiter_AW_L2==true -> 
            // wait till we get the lock
            ((MY_L2_STATUS <= ACQUIRE_PARENT));
            atomic {
              if
              :: MY_L2_STATUS < ACQUIRE_PARENT -> goto DONE_ACQUIRE_L2; // got the global lock just in time
              :: MY_L2_STATUS == ACQUIRE_PARENT -> MY_L2_STATUS  = COHORT_START ; //got a prefix of locks, compete at L3
              fi
            };
            // Compete at the next level (we come here only from prevStatus_Acq_L2 == ACQUIRE_PARENT case
            AcquireL3(abortedLevel_Acq_L2); 
          ::waiter_AW_L2==false ->
            // Timed out, Start to abandon
            SWAP(MY_L2_STATUS, prevStatus_Acq_L2 , ABANDONED);
            atomic {
              if
              :: prevStatus_Acq_L2 < ACQUIRE_PARENT -> MY_L2_STATUS  = prevStatus_Acq_L2 ; goto DONE_ACQUIRE_L2; // got the global lock just in time
              :: prevStatus_Acq_L2 == ACQUIRE_PARENT -> MY_L2_STATUS  = COHORT_START ; //got a prefix of locks, compete at L3
              :: else -> abortedLevel_Acq_L2 = 1 /* L2 */; goto DONE_ACQUIRE_L2; // Aborted here (levels are numbered 0, 1, 2, hence this is L2's numerical value is 1)
              fi
            };
            // Compete at the next level (we come here only from prevStatus_Acq_L2 == ACQUIRE_PARENT case
            AcquireL3(abortedLevel_Acq_L2); 
          fi // non-determinism
       fi // impatient 
    fi // no pred

    DONE_ACQUIRE_L2: skip;
}

inline AttemptToRelinquishLockL2(me_DWR_L2 /* destroyed */, prev_DWR_L2 /* destroyed and used in caller */, waiter_DWR_L2){
    bool retOld_DWR_L2;
    byte tmpStatus_DWR_L2;
    byte tmpSucc_DWR_L2;
    do
    :: d_step{else ->
       // CAS L2 to null
       BOOL_CAS(L2, me_DWR_L2, NONE, retOld_DWR_L2);};
       if 
       :: retOld_DWR_L2 == false -> // Failed to CAS the tail pointer
          if
          :: L2_STATUS(me_DWR_L2) == COHORT_START -> // We had acquired this level by competing. 
             L2_STATUS(me_DWR_L2) = ACQUIRE_PARENT; // Set the status to ACQUIRE_PARENT so that  we can leave the qnode if we become impatient during release.
          :: d_step{ else -> skip; };
          fi
          // Can't wait for next to be updated, attempt to set IMPATIENT
          if
          :: waiter_DWR_L2 == true -> L2_NEXT(me_DWR_L2) != NONE; retOld_DWR_L2=false;
          :: waiter_DWR_L2 == false -> BOOL_CAS(L2_NEXT(me_DWR_L2), NONE, IMPATIENT, retOld_DWR_L2); 
          fi
          //BOOL_CAS(L2_NEXT(me_DWR_L2), NONE, IMPATIENT, retOld_DWR_L2); 
          if 
          :: d_step{retOld_DWR_L2 == false -> // CAS failed, I have a successor enqueued now.
             // try to pass the lock to the successor
             SWAP(L2_STATUS(L2_NEXT(me_DWR_L2)), tmpStatus_DWR_L2, ACQUIRE_PARENT);};
             if
             ::d_step{ tmpStatus_DWR_L2 == ABANDONED -> 
               // Successor already abandoned!
               // Keep looking
               tmpSucc_DWR_L2 = L2_NEXT(me_DWR_L2);};
               d_step{
                L2_NEXT(me_DWR_L2) = prev_DWR_L2;
                prev_DWR_L2 = me_DWR_L2;
                me_DWR_L2 =     tmpSucc_DWR_L2;
               }
             :: atomic {else -> L2_STATUS(me_DWR_L2) = RECYCLED; break;}; // Gosh! passed the lock, recycle me and end this circus.
             fi
          ::atomic{ else -> break;} //CAS success, leaving.
          fi
       :: atomic {else -> L2_STATUS(me_DWR_L2) = RECYCLED; break;}; // Passed the lock, hence recycle the last node.
       fi
    od
}

// Recycle all nodes on which we had stepped
inline RecyclePredecessorsL2(node_CRC_L2 /* destroyed */, pprev_CRC_L2 /* local var */){
    do
    :: d_step{node_CRC_L2 != NONE ->
       pprev_CRC_L2 = L2_NEXT(node_CRC_L2);};
       d_step{
        L2_STATUS(node_CRC_L2) = RECYCLED;
        node_CRC_L2 = pprev_CRC_L2;
       }
    :: atomic {else -> break;};
    od
}

// Look for an unabandoned successor at L2 to pass the lock
inline PassToPeerOnReleaseL2(value_HHP_L2 /* const */, waiter_HHP_L2){
    byte prev_HHP_L2 = NONE;
    byte curNode_HHP_L2 = myL2Id;
    byte succTmp_HHP_L2;
    byte prevStatus_HHP_L2;

    do
    :: else ->
       if
       :: HAS_VALID_L2_SUCC(curNode_HHP_L2) ->
          // try to pass the lock to the successor
          SWAP(L2_STATUS(L2_NEXT(curNode_HHP_L2)), prevStatus_HHP_L2,  value_HHP_L2);
          if
          :: d_step{ prevStatus_HHP_L2 == ABANDONED ->
             // Successor already abandoned!
             // Keep looking
             succTmp_HHP_L2 = L2_NEXT(curNode_HHP_L2);};
             d_step {
              L2_NEXT(curNode_HHP_L2) = prev_HHP_L2;
              prev_HHP_L2 = curNode_HHP_L2;
              curNode_HHP_L2 = succTmp_HHP_L2;}
          :: atomic { else -> L2_STATUS(curNode_HHP_L2) = RECYCLED; break;}; // Lock passed, Recycle the last node.
          fi
        :: else ->  // no known succesor, release L3 lock 
                    ReleaseL3(); 
                    // Relinquish L2 lock
                    AttemptToRelinquishLockL2(curNode_HHP_L2, prev_HHP_L2, waiter_HHP_L2); 
                    break; 
        fi
    od

    byte pprev_HHP_L2;
    //Recycle all L2 nodes on which we had stepped
    RecyclePredecessorsL2(prev_HHP_L2, pprev_HHP_L2);
}


inline PassToParentOnTimeoutL3(abortedLevel_HVA_L3) {
    d_step{
        if
        :: abortedLevel_HVA_L3 == 2 /* L3 */ -> skip;
        :: else -> skip; /* Never happens PassToPeerOnTimeoutL3(abortedLevel_HVA_L3); */
        fi
    }
}


// Pass the lock prefix to a successor at L2 
inline PassToPeerOnTimeoutL2(abortedLevel_HHA_L2, waiter_HHA_L2){
    byte prev_HHA_L2 = NONE;
    byte curNode_HHA_L2 = myL2Id;
    byte prevStatus_HHA_L2;
    byte succTmp_HHA_L2;
    do
    :: else ->
       if
       :: HAS_VALID_L2_SUCC(curNode_HHA_L2) ->
          // try to pass the lock to the successor
          SWAP(L2_STATUS(L2_NEXT(curNode_HHA_L2)), prevStatus_HHA_L2,  ACQUIRE_PARENT);
          if
          :: d_step { prevStatus_HHA_L2 == ABANDONED ->
             // Successor already abandoned!
             // Keep looking
             succTmp_HHA_L2 = L2_NEXT(curNode_HHA_L2);};
             d_step {
              L2_NEXT(curNode_HHA_L2) = prev_HHA_L2;
              prev_HHA_L2 = curNode_HHA_L2;
              curNode_HHA_L2 = succTmp_HHA_L2;}
           :: atomic {else -> L2_STATUS(curNode_HHA_L2) = RECYCLED; break;}; // Lock passed, Recycle the last node.
           fi
       :: else ->  //  no known succesor, go to next level (in this case we will simply come back)
                   PassToParentOnTimeoutL3(abortedLevel_HHA_L2); 
                   // Relinquish L2 lock
                   AttemptToRelinquishLockL2(curNode_HHA_L2, prev_HHA_L2, waiter_HHA_L2); 
                   break;
       fi
    od
    //Recycle all L2 nodes on which we had stepped
    byte pprev_HHA_L2;
    RecyclePredecessorsL2(prev_HHA_L2, pprev_HHA_L2);
}


inline PassToParentOnTimeoutL2(abortedLevel_HVA_L2, waiter_HVA_L2) {
    if
    :: d_step {abortedLevel_HVA_L2 == 1 /* L2 */ -> skip;} // if this is the level where we had abandoned, return.
    :: else -> PassToPeerOnTimeoutL2(abortedLevel_HVA_L2, waiter_HVA_L2); // Find a waiting successor at L2
    fi
}


inline ReleaseL2(waiter_Rel_L2) {
    byte curCount_Rel_L2 = MY_L2_STATUS;
    byte succ_Rel_L2;
    byte prev_Rel_L2 = NONE;
    byte copyMyL2Id = myL2Id;
    byte newCurCount_Rel_L2 = curCount_Rel_L2 +1;
    byte pprev_tmp1_HHA_L2;

    if
    :: curCount_Rel_L2 == THRESHOLD -> 
       // Release L3 lock since we can't keep passing at L2 anymore
       ReleaseL3(); 
       // Relinquish L2 lock
       AttemptToRelinquishLockL2(copyMyL2Id, prev_Rel_L2, waiter_Rel_L2);
       //Recycle all L2 nodes on which we had stepped
       RecyclePredecessorsL2(prev_Rel_L2, pprev_tmp1_HHA_L2);
    :: else ->
           // Pass the lock to a L2 peer. 
           PassToPeerOnReleaseL2(newCurCount_Rel_L2, waiter_Rel_L2);
    fi
}


inline AcquireWrapperL2(acquired_AW_L2) {
    byte abortedLevel_AW_L2 = NONE;

    // Non-deterministically decide to wait
    if
    ::true-> AcquireL2(abortedLevel_AW_L2, true); assert(abortedLevel_AW_L2==NONE || abortedLevel_AW_L2==2);
    ::true-> AcquireL2(abortedLevel_AW_L2, false);
    fi;

    if
    :: d_step{ abortedLevel_AW_L2==NONE -> // Successfully acquire, return true
       acquired_AW_L2=true; };
    :: d_step{ else -> /* abandoned */ acquired_AW_L2=false;}; 
       // Release acquired lock prefix
       PassToParentOnTimeoutL2(abortedLevel_AW_L2, false); 
    fi
}

inline ReleaseL3() {
  skip;
}

inline AcquireL1(abortedLevel_Acq_L1, waiter_AW_L1) {
  byte prevStatus_Acq_L1;
  byte pred_Acq_L1;
  byte predStat_Acq_L1;
  byte tmpStatus_Acq_L1;
  SWAP(MY_L1_STATUS, prevStatus_Acq_L1, WAIT);

  atomic{
    if
    :: prevStatus_Acq_L1 == ABANDONED -> goto START_SPIN_L1; // Reentry after abandonment
    :: prevStatus_Acq_L1 == COHORT_START -> goto  GOT_LOCK_L1; // Never happens
    :: prevStatus_Acq_L1 == WAIT -> MY_L1_NEXT = NONE; goto USE_QNODE_L1; // Never happens
    :: prevStatus_Acq_L1 == RECYCLED -> MY_L1_NEXT = NONE; goto USE_QNODE_L1; // Ready to enqueue 
    :: else -> 
       // Lock passed after abandonment. Wait till the status becomes RECYCLED
         if
         :: waiter_AW_L1 == true -> MY_L1_STATUS == RECYCLED; tmpStatus_Acq_L1=RECYCLED;
         :: waiter_AW_L1 == false -> CAS(MY_L1_STATUS, WAIT, ACQUIRE_PARENT, tmpStatus_Acq_L1);
         fi;


       // Timeout..
       //CAS(MY_L1_STATUS, WAIT, ACQUIRE_PARENT, tmpStatus_Acq_L1);
       if
       :: tmpStatus_Acq_L1 != RECYCLED -> abortedLevel_Acq_L1 = 0 /* L1 */;  // abandoned at L1 (numerically numered as 0)
          goto DONE_ACQUIRE_L1;
       ::else -> skip; // RECYCLED just in time.
       fi;
    fi;
};
  /** Happens only from else ***/
  /*while(I->status != RECYCLED); No unbounded wait*/
  // Init next field
  MY_L1_NEXT = NONE;
USE_QNODE_L1: skip;
  /**** already set MY_L1_NEXT = NONE; ****/
  // swap tail pointer
  SWAP(L1,pred_Acq_L1, myL1Id);
  if
  :: atomic{ pred_Acq_L1 == NONE ->
GOT_LOCK_L1: 
     // No predecessor.
     // Set the status to COHORT_START   
     MY_L1_STATUS = COHORT_START; 
     /* check correctness */
     inCSL1++;
     };
     /* check correctness so that we are the only one from level 1 to have acquired the L1 lock*/
     d_step{ assert(inCSL1 == 1); 
      inCSL1--;};

     // Proceed to acquire L2 lock
     AcquireL2(abortedLevel_Acq_L1, waiter_AW_L1);
  :: else ->
      // Have a predecessor, swap my id with pred->next
      /* Avoid unbounded wait for I->next */
      SWAP(L1_NEXT(pred_Acq_L1), predStat_Acq_L1, myL1Id);
      if
      :: d_step {predStat_Acq_L1 == IMPATIENT ->
         // Pred had already left having become impatient, recycle pred  
         L1_STATUS(pred_Acq_L1)= RECYCLED;};
         d_step{
          MY_L1_STATUS = COHORT_START; // We are the lock owner now
          /* check correctness */
          inCSL1++;
         };
         /* check correctness so that we are the only one from level 1 to have acquired the L1 lock*/
         d_step{ assert(inCSL1 == 1); inCSL1--;};
         // Proceed to acquire L2 lock
         AcquireL2(abortedLevel_Acq_L1, waiter_AW_L1);
      ::  else -> 
START_SPIN_L1: skip;

           if
           ::waiter_AW_L1==true -> 
             ((MY_L1_STATUS <= ACQUIRE_PARENT) ) ;
             atomic{
               if
               :: MY_L1_STATUS < ACQUIRE_PARENT -> abortedLevel_Acq_L1 = NONE;  goto DONE_ACQUIRE_L1; // Got the global lock just in time.
               :: MY_L1_STATUS == ACQUIRE_PARENT -> MY_L1_STATUS  = COHORT_START; /* check correctness */ inCSL1++; // Got only the local lock
               fi
             };
             /* check correctness so that we are the only one from level 1 to have acquired the L1 lock*/
             d_step{ assert(inCSL1 == 1);  inCSL1--;};
             // Proceed to acquire L2 lock
             AcquireL2(abortedLevel_Acq_L1, waiter_AW_L1); 
           ::waiter_AW_L1==false-> 
             // Waited long enough, timeout and  try to abandon
             SWAP(MY_L1_STATUS, prevStatus_Acq_L1 , ABANDONED); 
             atomic{
               if
               :: prevStatus_Acq_L1 < ACQUIRE_PARENT -> MY_L1_STATUS  = prevStatus_Acq_L1; abortedLevel_Acq_L1 = NONE;  goto DONE_ACQUIRE_L1; // Got the global lock just in time.
               :: prevStatus_Acq_L1 == ACQUIRE_PARENT -> MY_L1_STATUS  = COHORT_START; /* check correctness */ inCSL1++; // Got only the local lock
               :: else -> abortedLevel_Acq_L1 = 0 /* L1 */; goto DONE_ACQUIRE_L1; // successfully abandoned at L1
               fi
             };
             /* executed iff prevStatus_Acq_L1 == ACQUIRE_PARENT */

             /* check correctness so that we are the only one from level 1 to have acquired the L1 lock*/
             d_step{ assert(inCSL1 == 1);  inCSL1--;};
             // Proceed to acquire L2 lock
             AcquireL2(abortedLevel_Acq_L1, waiter_AW_L1); 
           fi // non-determinism
         fi // Impatient
       fi // 
  DONE_ACQUIRE_L1: skip;
}

// Attempts to set L1 lock to null but if it cannot, it tries to pass the L1 lock to a successor.
inline AttemptToRelinquishLockL1(me_DWR_L1 /* destroyed */, prev_DWR_L1 /* destroyed and used in caller */, waiter_DWR_L1){
  bool retOld_DWR_L1;
  byte tmpStatus_DWR_L1;
  byte tmpSucc_DWR_L1;
  do
  :: d_step{else ->
     // Try to set L1 lock to none
     BOOL_CAS(L1, me_DWR_L1, NONE, retOld_DWR_L1);};
     if 
     :: retOld_DWR_L1 == false -> // A successor enqueued just in time.
        if
        :: L1_STATUS(me_DWR_L1) == COHORT_START -> // We had acquired this level by competing.
           L1_STATUS(me_DWR_L1) = ACQUIRE_PARENT; // Set the status to ACQUIRE_PARENT so that  we can leave the qnode if we become impatient during release.
        :: d_step { else -> skip; };
        fi
        // Can't wait for the successor to update next. Leaving impatiently.
        if
        :: waiter_DWR_L1 == true -> L1_NEXT(me_DWR_L1) != NONE; retOld_DWR_L1=false;
        :: waiter_DWR_L1 == false -> BOOL_CAS(L1_NEXT(me_DWR_L1), NONE, IMPATIENT, retOld_DWR_L1); 
        fi
        //BOOL_CAS(L1_NEXT(me_DWR_L1), NONE, IMPATIENT, retOld_DWR_L1); 
        if 
        :: d_step{retOld_DWR_L1 == false ->
           // Successor updated the next pointer just in time
           SWAP(L1_STATUS(L1_NEXT(me_DWR_L1)), tmpStatus_DWR_L1, ACQUIRE_PARENT);};
           if
           :: d_step{tmpStatus_DWR_L1 == ABANDONED ->
              // Successor already abandoned!
              // Keep looking
              tmpSucc_DWR_L1 = L1_NEXT(me_DWR_L1);};
              d_step{
                L1_NEXT(me_DWR_L1) = prev_DWR_L1;
                prev_DWR_L1 = me_DWR_L1;
                me_DWR_L1 =   tmpSucc_DWR_L1;};
           :: atomic{else -> L1_STATUS(me_DWR_L1) = RECYCLED; break; }; // Gosh! passed the lock, recycle me.
           fi
        :: atomic{ else -> break; }
        fi
      :: atomic{else -> L1_STATUS(me_DWR_L1) = RECYCLED; break; };  // Passed the lock, hence recycle the last node.
      fi
  od
}

//Recycle all L1 nodes on which we had stepped
inline RecyclePredecessorsL1(node_CRC_L1 /* destroyed */, pprev_CRC_L1 /* local var */){
  do
  :: d_step{ node_CRC_L1 != NONE ->
    pprev_CRC_L1 = L1_NEXT(node_CRC_L1); };
    d_step{
      L1_STATUS(node_CRC_L1) = RECYCLED;
      node_CRC_L1 = pprev_CRC_L1;
    };
  :: atomic{ else -> break; };
  od
}


// Called to release a lock at L1
inline PassToPeerOnReleaseL1(value_HHP_L1 /* const */, waiter_HHP_L1){
  byte prev_HHP_L1 = NONE;
  byte curNode_HHP_L1 = myL1Id;
  byte succTmp_HHP_L1; 
  byte prevStatus_HHP_L1;

  do
    :: else ->
       if
       :: HAS_VALID_L1_SUCC(curNode_HHP_L1) ->
          // have a known successor, try to release the lock to it.
         SWAP(L1_STATUS(L1_NEXT(curNode_HHP_L1)), prevStatus_HHP_L1,  value_HHP_L1);
          if
          :: d_step{prevStatus_HHP_L1 == ABANDONED ->
             // Successor already abandoned!
             // Keep looking
             succTmp_HHP_L1 = L1_NEXT(curNode_HHP_L1);};
             d_step {
                L1_NEXT(curNode_HHP_L1) = prev_HHP_L1;
                prev_HHP_L1 = curNode_HHP_L1;
                curNode_HHP_L1 = succTmp_HHP_L1;};
          :: atomic{else -> L1_STATUS(curNode_HHP_L1) = RECYCLED; break; };
          fi
        :: else ->  ReleaseL2(waiter_HHP_L1); AttemptToRelinquishLockL1(curNode_HHP_L1, prev_HHP_L1, waiter_HHP_L1); break; // Lock passed, Recycle the last node.
      fi
  od

  byte pprev_HHP_L1;
  //Recycle all L1 nodes on which we had stepped
  RecyclePredecessorsL1(prev_HHP_L1, pprev_HHP_L1);
}


inline PassToPeerOnTimeoutL1(abortedLevel_HHA_L1, waiter_HHA_L1){
  byte prev_HHA_L1 = NONE;
  byte curNode_HHA_L1 = myL1Id;
  byte prevStatus_HHA_L1;
  byte succTmp_HHA_L1;
  do
    :: else ->
      if
      :: HAS_VALID_L1_SUCC(curNode_HHA_L1) ->
        // have a known successor, try to release the lock to it.
         SWAP(L1_STATUS(L1_NEXT(curNode_HHA_L1)), prevStatus_HHA_L1,  ACQUIRE_PARENT);
         if
         :: d_step{prevStatus_HHA_L1 == ABANDONED ->
            // Successor already abandoned!
            // Keep looking
            succTmp_HHA_L1 = L1_NEXT(curNode_HHA_L1);};
            d_step {
                L1_NEXT(curNode_HHA_L1) = prev_HHA_L1;
                prev_HHA_L1 = curNode_HHA_L1;
                curNode_HHA_L1 = succTmp_HHA_L1;};
         :: atomic{else -> L1_STATUS(curNode_HHA_L1) = RECYCLED;break; }; // Lock passed, Recycle the last node.
         fi
      :: else ->
         // no known succesor, release L2 lock
         PassToParentOnTimeoutL2(abortedLevel_HHA_L1, waiter_HHA_L1);
         // Relinquish L1 lock
         AttemptToRelinquishLockL1(curNode_HHA_L1, prev_HHA_L1, waiter_HHA_L1); break;
      fi
  od

  //Recycle all L1 nodes on which we had stepped
  byte pprev_HHA_L1;
  RecyclePredecessorsL1(prev_HHA_L1, pprev_HHA_L1);
}

inline PassToParentOnTimeoutL1(abortedLevel_HVA_L1, waiter_HVA_L1) {
  if
  :: d_step{ abortedLevel_HVA_L1 == 0 /* L1 */ -> skip; }; // We abandoned at L1, (numerically number 0), hence nothing to do.
  :: else -> PassToPeerOnTimeoutL1(abortedLevel_HVA_L1, waiter_HVA_L1);   // Pass lock prefixes to a L1 peer because we abandoned at a higher level.
  fi
}


inline ReleaseL1(waiter_Rel_L1) {
  byte curCount_Rel_L1 = MY_L1_STATUS;
  byte succ_Rel_L1;
  byte prev_Rel_L1 = NONE;
  byte copyMyL1Id = myL1Id;
  byte newCurCount_Rel_L1 = curCount_Rel_L1 +1;
  byte pprev_tmp1_HHA_L1;

  if
  :: curCount_Rel_L1 == THRESHOLD ->
        // Reaching the passing threshold at L1, hence release L2 first
        ReleaseL2(waiter_Rel_L1);
        // Relinquish L1
        AttemptToRelinquishLockL1(copyMyL1Id, prev_Rel_L1, waiter_Rel_L1);
        //Recycle all L1 nodes on which we had stepped
        RecyclePredecessorsL1(prev_Rel_L1, pprev_tmp1_HHA_L1);
  :: else ->
    // pass the global lock within L1 domain
    PassToPeerOnReleaseL1(newCurCount_Rel_L1, waiter_Rel_L1);
  fi
}



inline AcquireWrapperL1(acquired_AW_L1) {
  byte abortedLevel_AW_L1 = NONE;
  // Non-deterministically decide to wait
  if
  ::true->  AcquireL1(abortedLevel_AW_L1, true); assert((abortedLevel_AW_L1==NONE) || (abortedLevel_AW_L1==2));
  ::true->  AcquireL1(abortedLevel_AW_L1, false);
  fi;
  if
  :: d_step{abortedLevel_AW_L1==NONE -> // Successfully acquired, return true
        acquired_AW_L1=true;};
  :: d_step{else -> acquired_AW_L1=false;};
     // Timed out at some level. Release acquired locks.
     PassToParentOnTimeoutL1(abortedLevel_AW_L1, false /* no wait */);
  fi
}


// Validate thatteh status of all Qnodes is in RECYCLED state.
inline EnsureAllinRState(){
    byte index;
    for(index: 0..(MAX_L1_THREADS-1)){
      assert(L1_STATUS(index) == RECYCLED);
      assert(L1_NEXT(index) != IMPATIENT);
    }
    for(index: 0..(MAX_L2_THREADS-1)){
      assert(L2_STATUS(index) == RECYCLED);
      assert(L2_NEXT(index) != IMPATIENT);
    }
}

// For threads that start at L1
proctype  WorkObserved(int myId) { 
  bool acquired;
  byte myL1Id;
  byte myL2Id;

  d_step{
   myL1Id = MY_L1_NODE_ID(myId);
   myL2Id = MY_L2_NODE_ID(myId);
  };

  AcquireWrapperL1(acquired);

  if
  :: acquired -> 
     // Non-deterministically decide to wait
     if
     ::true-> ReleaseL1(true); assert(MY_L1_STATUS==RECYCLED);
     ::true-> ReleaseL1(false);
     fi;
  :: d_step{else -> skip;}; // Acquisition failed.
  fi
  done++;
}

// For threads that start at L2
proctype  WorkLevel2(int myId)  {
  bool acquired;
  byte myL1Id;
  byte myL2Id;

  d_step{
    myL1Id = MY_L1_NODE_ID(myId);
    myL2Id = MY_L2_NODE_ID(myId);
  };

  AcquireWrapperL2(acquired);
  if
  :: acquired -> 
     // Non-deterministically decide to wait
     if
     ::true-> ReleaseL2(true); assert(MY_L2_STATUS==RECYCLED);
     ::true-> ReleaseL2(false);
     fi;
  :: d_step{else -> skip;}; // Acquisition failed.
  fi
  done++;
}
 
 
init {
  /* init */
      d_step{
        // Initialize tail pointers
        L1 = NONE;
        L2 = NONE;
        byte i;
        // Initialize qnodes
        for(i: 0..(MAX_L1_THREADS-1)){
          L1_NEXT(i) = NONE;
          L1_STATUS(i) = RECYCLED;
        }
        for(i: 0..(MAX_L2_THREADS-1)){
          L2_NEXT(i) = NONE;
          L2_STATUS(i) = RECYCLED;
        }
      }
  // 4 threads
  // 2 threads start at level 1 (numerically level 0)
  run WorkObserved(0); 
  run WorkObserved(1); 
  // 2 threads start at level 2 (numerically level 1)
  run WorkLevel2(2);
  run WorkLevel2(3); 
  // Wait till all done (or assert if dead locked)
  done==4;
  // Verify that all qnodes end in RECYCLED state
  EnsureAllinRState();
// Verify that in any interleaving at least one thread succeeds in entering the critical section
  assert(totalAcquisitions >= 1);
} 



