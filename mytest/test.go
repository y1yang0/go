package main

// /// loop roate

//go:noinline
func whatthefuck(t1 []int8, t2 []int) int {
	r := 0
	for i := 0; i <= 128; i++ {
		// t1[3] = 5
		r += t2[2]
		t2[1] = 33
		t2[3] = 44
		t2[i%2] = 0
	}
	return r
}

func whatthefuck333(cnt int, t2 []int) int {
	r := 0
	if 0 <= cnt {
		if len(t2) <= 5 {
			panic("oops")
		}
		for i := 0; i <= cnt; i++ {
			// t1[3] = 5
			r += t2[5]
		}
	}
	return r
}

// var p *int

// //go:noinline
// func tt(t1 []int, t2 []int) int {
// 	r := 0
// 	for i := 0; i <= 128; i++ {
// 		p = &t1[5]
// 		*p = 33
// 		r += t2[5]
// 	}
// 	return r
// }

// // go:noinline
// func t3(s string, q string) int {
// 	r := 4
// 	for i := 0; i < len(s); i++ {
// 		r += int(s[4])
// 		r += int(q[2])
// 	}
// 	return r
// }

// var tk [256]byte

//go:noinline
// func fu(b *[16]byte) {
// 	max := len(*b)
// 	for _, _ := range b {
// 		// fmt.Printf("%v %v", i, v)
// 		(*b)[4] = max
// 	}
// }

//go:noinline
// func t6() int {

//		r := 0
//		for i := 0; i < 155; i++ {
//			var p [2]int
//			add := (*[1]int)(p[:])
//			r += add[0]
//			// p = (*[2]int)(a[:])
//			// q := (*[2]int)(a[1:])
//			// *p = *q
//		}
//		return r
//	}

//go:noinline
func ss() int {
	return 43
}

type st struct {
	next *st
	val  int
}

//go:noinline
func whatthefuckoops(p *st) {
	for i := p; i != nil; i = i.next {
		i.val = 33
	}
}

func whatthefuck55(v int64, div int32, rem *int32) int32 {
	println("==before", v, div, *rem)
	res := int32(0)
	for bit := 30; bit >= 0; bit-- {
		if v >= int64(div)<<uint(bit) {
			v = v - (int64(div) << uint(bit))
			// Before this for loop, res was 0, thus all these
			// power of 2 increments are now just bitsets.
			res |= 1 << uint(bit)
		}
	}
	if v >= int64(div) {
		if rem != nil {
			*rem = 0
		}
		println("==after1", v, div, *rem)
		return 0x7fffffff
	}
	if rem != nil {
		*rem = int32(v)
	}
	println("==after2", v, div, *rem)
	return res
}

func whatthefuckfff() (i int) {
	for first := true; first; first = false {
		i++
	}
	return
}

func whatthefuck_55(in <-chan int, out chan<- int, prime int) {
	for {
		i := <-in // Receive value of new variable 'i' from 'in'.
		if i%prime != 0 {
			out <- i // Send 'i' to channel 'out'.
		}
	}
}

func whatthefuck11424(s string, c byte) int {
	for i := 0; i < len(s); i++ {
		if s[i] == c {
			return i
		}
	}
	return -1
}

func whatthefuck111(x, y, z int) int {
	a := 0
	// if y == 0 { // ERROR "Branch prediction rule default < call"
	// 	y = g(y, z, x)
	// } else {
	// 	y++
	// }
	// if y == x { // ERROR "Branch prediction rule default < call"
	// 	y = g(y, z, x)
	// } else {
	// }
	// if y == 2 { // ERROR "Branch prediction rule default < call"
	// 	z++
	// } else {
	// 	y = g(z, x, y)
	// }
	// if y+z == 3 { // ERROR "Branch prediction rule call < exit"
	// 	println("ha ha")
	// } else {
	// 	panic("help help help")
	// }
	if x != 0 { // ERROR "Branch prediction rule default < ret"
		for i := 0; i < x; i++ { // ERROR "Branch prediction rule stay in loop"
			if x == 4 { // ERROR "Branch prediction rule stay in loop"
				return a
			}
			for j := 0; j < y; j++ { // ERROR "Branch prediction rule stay in loop"
				for k := 0; k < z; k++ { // ERROR "Branch prediction rule stay in loop"
					a -= j * i
				}
				a += j
			}
		}
	}
	return a
}

func main() {
	tx := []int8{3, 3, 5, 5}
	tx1 := []int{3, 3, 5, 5}
	whatthefuck(tx, tx1)
	// whatthefuck("aaaa", 3)
	// whatthefuck(3, 5, 62)
	// whatthefuck(12345*1000000000+54321, 1000000000, &e)
	// 创建两个整数类型的通道
	// in := make(chan int)
	// out := make(chan int)

	// prime := 2 // 设置质数

	// go whatthefuck(in, out, prime) // 在一个单独的 Goroutine 中调用函数

	// // 向 'in' 通道发送一些值
	// for i := 2; i <= 10; i++ {
	// 	in <- i
	// }

	// // 从 'out' 通道接收并打印结果
	// for i := 2; i <= 10; i++ {
	// 	result := <-out
	// 	fmt.Println(result)
	// }

	// arr := []int{33, 5, 6, 2}
	// st := SS{3, 5}
	// t1([]int8{5, 6, 6, 6, 4}, arr)
	// t3("helloworld", "oopsoopsoops")
	// var btss [16]byte
	// t6()
	// fmt.Println("==%v", tk)
}
