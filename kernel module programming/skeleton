#include <linux/fs.h> 
#include <linux/init.h> 
#include <linux/kobject.h> 
#include <linux/module.h> 
#include <linux/string.h> 
#include <linux/sysfs.h> 
 
static struct kobject *mymodule; 
 

struct my_operations {
	/* 작성 */
};


int myvariable = 0; 
EXPORT_SYMBOL(myvariable);

static ssize_t mytraverse (char *buf)
{
    return sprintf(buf, "%d\n", myvariable); 
}
static ssize_t myinsert (char *buf, size_t count)
{
    sscanf(buf, "%du", &myvariable); 
    return count;
}

static struct my_operations default_op = {
	/* 작성 */
};

struct my_operations *myop;
EXPORT_SYMBOL(myop);
 
static ssize_t myvariable_show(struct kobject *kobj, 
                               struct kobj_attribute *attr, char *buf) 
{ 
	/* 작성 */
} 
 
static ssize_t myvariable_store(struct kobject *kobj, 
                                struct kobj_attribute *attr, char *buf, 
                                size_t count) 
{ 
	/* 작성 */
} 
 
static struct kobj_attribute myvariable_attribute = 
    __ATTR(myvariable, 0660, myvariable_show, (void *)myvariable_store); 
 
static int __init mymodule_init(void) 
{ 
    int error = 0; 
 
    pr_info("mymodule: initialised\n"); 

	myop = &default_op;
 
    mymodule = kobject_create_and_add("mymodule", kernel_kobj); 
    if (!mymodule) 
        return -ENOMEM; 
 
    error = sysfs_create_file(mymodule, &myvariable_attribute.attr); 
    if (error) { 
        pr_info("failed to create the myvariable file " 
                "in /sys/kernel/mymodule\n"); 
    } 
 
    return error; 
} 
 
static void __exit mymodule_exit(void) 
{ 
    pr_info("mymodule: Exit success\n"); 
    kobject_put(mymodule); 
} 
 
module_init(mymodule_init); 
module_exit(mymodule_exit); 

 
MODULE_LICENSE("GPL");
