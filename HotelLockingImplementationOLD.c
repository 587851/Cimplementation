#include "stdbool.h"
#include "stdio.h"
#include "stdlib.h"
#include "string.h"

struct room
{
    int roomNumber;
    struct key *keys;
    int currentKeyIndex;
    int totalKeys;
    struct guest *currentOccupant;
    int lastKeyIndex;
};

struct key
{
    int value;
};

struct guest
{
    char name[20];
    struct key keys[100];
    int totalKeys;
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
        r->keys[i].value = roomNumber * 10 + i;
    }
    r->totalKeys = numKeys;
    r->currentKeyIndex = 0;
}
void freeRoom(struct room *r)
{
    free(r->keys);
    r->keys = NULL;
    r->totalKeys = 0;
    r->currentKeyIndex = 0;
    free(r);
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
        printf("Key %d: %d\n", i+1, g->keys[i].value);
        hasKeys = 1;
    }
    if (!hasKeys)
    {
        printf("No keys\n\n");
    }
}

void checkIn(struct guest *g, struct room *r)
{
    if (r->currentOccupant == NULL)
    {
        if (r->currentKeyIndex < r-> totalKeys - 1)
        {
            int currentRoomKeyIndex = r->currentKeyIndex;
            g->keys[g->totalKeys] = r->keys[currentRoomKeyIndex + 1];
            g->totalKeys++;

            r->currentOccupant = g;
            printf("%s has checked into room %d.\n\n", g->name, r->roomNumber);
        }
    }
    else
    {
        printf("Room %d is already occupied by %s.\n\n", r->roomNumber, r->currentOccupant->name);
    }
}

void checkOut(struct guest *g, struct room *r)
{
    if (r->currentOccupant == g)
    {
        printf("%s has checked out from room %d.\n\n", r->currentOccupant->name, r->roomNumber);
        r->currentOccupant = NULL;
    }
    else
    {
        printf("Room %d is not currently occupied by %s.\n\n", r->roomNumber, g->name);
    }
}

void entry(struct guest *g, struct room *r, struct key *k)
{
    if (r->currentOccupant == g)
    {
        if (r->keys[r->currentKeyIndex].value == k->value)
        {
            printf("%s entered room %d using key %d.\n\n", g->name, r->roomNumber, k->value);
        }
        else if (r->keys[r->currentKeyIndex + 1].value == k->value)
        {
            r->currentKeyIndex++;
            printf("%s entered room for the first time. Current key updated to key %d for room %d.\n\n", g->name, r->keys[r->currentKeyIndex].value, r->roomNumber);
        }
        else
        {
            printf("%s used the wrong key %d to try to enter the room.\n\n", g->name, k->value);
        }
    }
    else
    {
        printf("%s is not the occupant of room %d.\n\n", g->name, r->roomNumber);
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    struct room r1, r2, r3;
    struct room *rooms[3] = {&r1, &r2, &r3};
    int roomCount = sizeof(rooms) / sizeof(rooms[0]);
    for (int i = 0; i < roomCount; i++)
    {
        initRoom(rooms[i], 101 + i, 100);
    }

    struct guest guests[2];
    strcpy(guests[0].name, "Anna");
    strcpy(guests[1].name, "Bob");
    int guestCount = sizeof(guests) / sizeof(guests[0]);

    for (int i = 0; i < guestCount; i++)
    {
        guests[i].totalKeys = 0;
        for (int j = 0; j < 100; j++)
        {
            guests[i].keys[j].value = 0;
        }
    }

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
                    printf("%d - %s\n", i + 1, guests[i].name);
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
                    checkIn(&guests[currentGuestIndex], rooms[roomChoiceCheckIn - 1]);
                }

                break;
            case 2:
                printf("\nChoose a room to check out from:\n");
                for (int i = 0; i < roomCount; i++)
                {
                    printf("%d - Room nr. %d - %s\n", i + 1, rooms[i]->roomNumber, rooms[i]->currentOccupant == NULL ? "Available" : "Occupied");
                }
                printf("%d - Go back\n", roomCount + 1);

                int roomChoiceCheckOut = getInputNumber(1, roomCount + 1);
                if (roomChoiceCheckOut != roomCount + 1)
                {
                    checkOut(&guests[currentGuestIndex], rooms[roomChoiceCheckOut - 1]);
                }
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
                    int guestKeyAmount = guests[currentGuestIndex].totalKeys;
                    printf("\nChoose a key to use:\n");
                    printGuestKeys(&guests[currentGuestIndex]); 
                    printf("%d - Go back\n", guestKeyAmount + 1);           
                    int keyChoice = getInputNumber(1, guestKeyAmount + 1);
                    if(keyChoice != guestKeyAmount + 1){
                        entry(&guests[currentGuestIndex], rooms[roomChoiceEntry - 1], &guests[currentGuestIndex].keys[keyChoice - 1]);
                    }                  
                }
                break;
            case 4:
                printGuestKeys(&guests[currentGuestIndex]);
                break;
            case 5:
                currentGuestIndex = -1;
                menuIndex = 0;
                break;
            }
            break;
        }
    }

    for (int i = 0; i < roomCount; i++)
    {
        freeRoom(rooms[i]);
    }

    printf("Program is stopped\n");
    return 0;
}
