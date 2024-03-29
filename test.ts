
// Dependent types
type ArrayLength<T, Length extends number> = [T, ...Array<T>] & { length: Length };

function sumaArray(array: ArrayLength<number, 3>): number {
    return array.reduce((acc, val) => acc + val, 0);
}

const array1: ArrayLength<number, 3> = [1, 2, 3]; 
const array2: ArrayLength<number, 4> = [1, 2, 3, 4]; 
const array3: ArrayLength<number, 2> = [1, 2]; 

for (let i = 0; i <= 3; i++) {
  console.log(array1[i]); // error because array1 has length 3, 1,2,3, undefined

}

console.log(sumaArray(array1)); 
// console.log(sumaArray(array2));  // error



// Recursive types


type List<T> = {
  value: T;
  next: List<T> | null;
}


const createLinkedList = <T>(values: T[]): List<T> | null  => {
  let list: List<T> | null = null;
  for (let i = values.length - 1; i >= 0; i--) {
    list = { value: values[i], next: list };
  }
  return list
}

const list = createLinkedList([1, 2, 3, 4, 5]);
console.log(list);

const linkedList: List<number> = {
  value: 1,
  next: {
    value: 2,
    next: {
      value: 3,
      next: null
    }
  }
}


// Polymorphic types (and ad-hoc polymorphism)

type Filter = {
  <T>(array: T[], f: (item: T) => boolean): T[]
}

const filter: Filter = (array, f) => {
  const result: Parameters<typeof f>[0][] = [];
 for (let i = 0; i < array.length; i++) {
    const item = array[i];
    if (f(item)) {
      result.push(item);
    }
  }
  return result;
}

console.log(filter([1, 2, 3, 4, 5], _ => _ > 2)); // [3, 4, 5]


function len(str: string): number;
function len(arr: any[]): number;
function len(x: any): number {
  return x.length;
}

console.log(len('hello')); // 5
console.log(len([1, 2, 3, 4, 5])); // 5