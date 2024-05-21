#include "stdbool.h"
#include "stdio.h"
#include "stdlib.h"
#include "string.h"

struct room
{
    int roomNumber;   // not in alloy
    struct key *keys; // linked list
    struct key *currentKey;
    int totalKeys; // not in alloy

    struct guest *currentOccupant; // in frontdesk
    struct key *lastKey;           // in frontdesk
};

struct key
{
    int value; // not in alloy
};

struct guest
{
    char name[20];    // not in alloy
    struct key *keys; // linked list
    int totalKeys;    // not in alloy
};

void initRoom(struct room *r, int roomNumber, int numKeys)
{
    r->roomNumber = roomNumber;
    r->keys = (struct key *)malloc(numKeys * sizeof(struct key));
    r->currentOccupant = NULL;
    if (r->keys == NULL)
    {
        printf("No more memory\n");
        return;
    }
    for (int i = 0; i < numKeys; i++)
    {
        r->keys[i].value = roomNumber * 1000 + i;
    }
    r->totalKeys = numKeys;
    r->currentKey = &r->keys[0];
    r->lastKey = &r->keys[0];
}
void freeRoom(struct room *r)
{
    free(r->keys);
    r->keys = NULL;
    r->totalKeys = 0;
    r->currentKey = NULL;
    r->lastKey = NULL;
    free(r);
}

void initGuest(struct guest *g, const char *name, int keyMemorySpace)
{
    strcpy(g->name, name);
    g->keys = (struct key *)malloc(keyMemorySpace * sizeof(struct key));
    g->totalKeys = 0;
    if (g->keys == NULL)
    {
        printf("No more memory\n");
    }
}

void freeGuest(struct guest *g)
{
    free(g->keys);
    g->keys = NULL;
    g->totalKeys = 0;
    free(g);
}

void init(struct room **rooms, int roomCount, struct guest **guests, int guestCount)
{
    // Init rooms
    for (int i = 0; i < roomCount; i++)
    {
        rooms[i] = malloc(sizeof(struct room));
        if (rooms[i] != NULL)
        {
            initRoom(rooms[i], 101 + i, 100);
        }
        else
        {
            printf("No more mem %d\n", i);
        }
    }

    // Init guests
    for (int j = 0; j < guestCount; j++)
    {
        guests[j] = malloc(sizeof(struct guest));
        if (guests[j] != NULL)
        {
            char guestName[30];
            sprintf(guestName, "Guest %d", j);
            initGuest(guests[j], guestName, 100);
        }
        else
        {
            printf("Failed to allocate memory for guest %d\n", j);
        }
    }
}

int getInputNumber(int startIndex, int endIndex)
{
    int number;
    int result;

    printf("Enter number between %d and %d: ", startIndex, endIndex);
    result = scanf("%d", &number);

    while (result != 1 || number < startIndex || number > endIndex)
    {
        while (getchar() != '\n')
            ;
        printf("Invalid input. Please enter a valid number: ");
        result = scanf("%d", &number);
    }

    return number;
}

void printGuestKeys(struct guest *g)
{
    printf("%s keys:\n", g->name);
    int hasKeys = 0;
    for (int i = 0; i < g->totalKeys; i++)
    {
        printf("Key %d: %d\n", i + 1, g->keys[i].value);
        hasKeys = 1;
    }
    if (!hasKeys)
    {
        printf("No keys\n\n");
    }
}

struct key *getNextKey(struct key *currentKey, struct key *keySet, int totalKeys)
{
    if (currentKey == NULL || keySet == NULL)
    {
        return NULL;
    }
    bool isInSet = false;
    int currentIndex = 0;
    while (currentIndex < totalKeys && !isInSet)
    {
        if (keySet[currentIndex].value == currentKey->value)
        {
            isInSet = true;
        }
        else
        {
            currentIndex++;
        }
    }
    if (!isInSet)
    {
        printf("Not present");
        return NULL;
    }
    return &keySet[currentIndex + 1];
}

bool isGuestOccupant(struct guest *g, struct room *r, struct key *k)
{
    if (r->currentOccupant == NULL)
    {
        printf("Room %d is not currently occupied.\n", r->roomNumber);
        return false;
    }
    else if (r->currentOccupant != g)
    {
        printf("%s is not the occupant of room %d.\n", g->name, r->roomNumber);
        return false;
    }
    else
    {
        printf("%s is an occupant of the room %d\n", g->name, r->roomNumber);
        return true;
    }
}

bool checkIn(struct guest *g, struct room *r, struct key *k)
{
    if (r->currentOccupant == NULL)
    {
        if (r->lastKey != &r->keys[r->totalKeys - 1])
        {
            r->currentOccupant = g;
            g->keys[g->totalKeys] = *k;
            g->totalKeys++;
            r->lastKey = k;

            printf("%s has checked into room %d.\n\n", g->name, r->roomNumber);
            return true;
        }
        else
        {
            printf("Room %d has no more keys.\n\n", r->roomNumber);
            return false;
        }
    }
    else
    {
        printf("Room %d is already occupied by %s.\n\n", r->roomNumber, r->currentOccupant->name);
        return false;
    }
}

void checkOut(struct guest *g, struct room **rooms, int roomCount)
{
    int roomsCheckOutFrom = 0;
    for (int i = 0; i < roomCount; i++)
    {
        if (rooms[i]->currentOccupant == g)
        {
            printf("%s has checked out from room %d.\n\n", rooms[i]->currentOccupant->name, rooms[i]->roomNumber);
            rooms[i]->currentOccupant = NULL;
            roomsCheckOutFrom++;
        }
    }
    if (roomsCheckOutFrom == 0)
    {
        printf("%s have no rooms to check out from\n\n", g->name);
    }
}

void entry(struct guest *g, struct room *r, struct key *k)
{
    if (r->currentKey->value == k->value)
    {
        printf("%s entered room %d using key %d.\n\n", g->name, r->roomNumber, k->value);
    }
    else if (getNextKey(r->currentKey, r->keys, r->totalKeys)->value == k->value)
    {
        r->currentKey = k;
        printf("%s entered room for the first time. Current key updated to key %d for room %d.\n\n", g->name, k->value, r->roomNumber);
    }
    else
    {
        printf("%s used the wrong key %d to try to enter the room.\n\n", g->name, k->value);
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    int roomCount = 3;
    struct room *rooms[3];

    int guestCount = 2;
    struct guest *guests[2];

    init(rooms, roomCount, guests, guestCount);

    int keepLooping = 1;
    int menuIndex = 0;
    int currentGuestIndex = -1;
    while (keepLooping)
    {
        switch (menuIndex)
        {
        case 0:

            printf("1 - Choose guest \n2 - Exit program\n");
            int inputNumber = getInputNumber(1, 2);

            switch (inputNumber)
            {
            case 1:
                for (int i = 0; i < guestCount; i++)
                {
                    printf("%d - %s\n", i + 1, guests[i]->name);
                }
                printf("%d - Exit program\n", guestCount + 1);
                int guestChoice = getInputNumber(1, guestCount + 1);

                if (guestChoice != guestCount + 1)
                {
                    currentGuestIndex = guestChoice - 1;
                    menuIndex = 1;
                }
                printf("\n");
                break;
            case 2:
                keepLooping = 0;
            }
            break;

        case 1:
            printf("1 - Check in to room \n2 - Check out of room \n3 - Enter room \n4 - Check current keys \n5 - Go back\n");
            int inputNumberAs = getInputNumber(1, 5);

            switch (inputNumberAs)
            {
            case 1:
                printf("\nChoose a room to check in to:\n");
                for (int i = 0; i < roomCount; i++)
                {
                    printf("%d - Room nr. %d - %s\n", i + 1, rooms[i]->roomNumber, rooms[i]->currentOccupant == NULL ? "Available" : "Occupied");
                }
                printf("%d - Go back\n", roomCount + 1);

                int roomChoiceCheckIn = getInputNumber(1, roomCount + 1);
                if (roomChoiceCheckIn != roomCount + 1)
                {
                    struct key *nextKey = getNextKey(rooms[roomChoiceCheckIn - 1]->lastKey, rooms[roomChoiceCheckIn - 1]->keys, rooms[roomChoiceCheckIn - 1]->totalKeys);
                    bool successfulCheckIn = checkIn(guests[currentGuestIndex], rooms[roomChoiceCheckIn - 1], nextKey);
                    ;
                    /**
                    if(successfulCheckIn){
                        entry(&guests[currentGuestIndex], rooms[roomChoiceCheckIn - 1], nextKey);
                    }
                    **/
                }
                break;
            case 2:
                checkOut(guests[currentGuestIndex], rooms, roomCount);
                break;
            case 3:
                printf("\nChoose a room to enter:\n");
                for (int i = 0; i < roomCount; i++)
                {
                    printf("%d - Room nr. %d - %s\n", i + 1, rooms[i]->roomNumber, rooms[i]->currentOccupant == NULL ? "Available" : "Occupied");
                }
                printf("%d - Go back\n", roomCount + 1);

                int roomChoiceEntry = getInputNumber(1, roomCount + 1);
                if (roomChoiceEntry != roomCount + 1)
                {
                    int guestKeyAmount = guests[currentGuestIndex]->totalKeys;
                    printf("\nChoose a key to use:\n");
                    printGuestKeys(guests[currentGuestIndex]);
                    printf("%d - Go back\n", guestKeyAmount + 1);
                    int keyChoice = getInputNumber(1, guestKeyAmount + 1);
                    if (keyChoice != guestKeyAmount + 1)
                    {
                        entry(guests[currentGuestIndex], rooms[roomChoiceEntry - 1], &guests[currentGuestIndex]->keys[keyChoice - 1]);
                    }
                }
                break;
            case 4:
                printGuestKeys(guests[currentGuestIndex]);
                break;
            case 5:
                currentGuestIndex = -1;
                menuIndex = 0;
                break;
            }
            break;
        }
    }

    //  assert();

    for (int i = 0; i < guestCount; i++)
    {
        freeGuest(guests[i]);
    }

    for (int i = 0; i < roomCount; i++)
    {
        freeRoom(rooms[i]);
    }

    printf("Program is stopped\n");
    return 0;
}
