open util/boolean

abstract sig Profile{
	name:Name
}


-- PERSON -----------------------------------------------
---------------------------------------------------------
//Pascal: should a user not  be able to block other users? (then we also have to add that blocking is not reflexive)

sig PersonalProfile extends Profile{
	eMail:one EMail,
	friends:set PersonalProfile,
	following:set Profile,
	posted: set Content,
	isMember: set Member,
	canSee: set Content
//Pascal: do we need a field set "newsfeed"?
//Pascal: we need a field for blocked users
}
fact symmetric_friends{all disjoint p,q:PersonalProfile | p in q.friends => q in p.friends}

sig Name{} 																				//Pascal: I would place this sig after "profile"
fact unique_names{all disjoint p,q:Profile | p.name != q.name} 	//Pascal: I would place this fact directly after "Profile"?
//fact names_are_connected{Name in Profile.name}   				    //Pascal: 1. do you think we need this fact? 2. from where do you get this term "connected"? (is this commonly used terminology?)

sig EMail{}
fact unique_Emails{all disjoint p,q:PersonalProfile | p.eMail != q.eMail} //Pascal: should this fact not be beneath "PersonalProfile"?
fact eMail_are_connected{EMail in PersonalProfile.eMail}

fact no_reflexiv_friends{all p:Profile | not p in p.friends} 
fact no_reflexiv_followers{all p:Profile | not p in p.following}






-- GROUP ----------------------------------------------
-------------------------------------------------------

--what can a group post? Pascal: a group posts nothing, members can post to a group ;)
sig GroupProfile extends Profile {
	posted: CommentableContent
}
fact groupcontent_is_public/privat{all g:GroupProfile,c:CommentableContent |
						c in g.posted => (c.visible = Public || c.visible = Private)}
 
--== is this true?
//Pascal: what exactly?
fact one_admin_per_group{some m:Member, g:GroupProfile | m.memberOf=g => isTrue[m.isAdmin]}

//can a member be member and follow a group?
//Pascal: i think he cant. "Users who are not members of a group can still follow the group"

sig Member {
	isAdmin:Bool,
	memberOf: one GroupProfile
}
fact unique_members{all disjoint p,q:PersonalProfile, m:Member | m in p.isMember => not m in q.isMember}
fact members_are_connected{Member in PersonalProfile.isMember}

fact only_once_member_of_a_group{
	all p:PersonalProfile, disjoint m,n:Member, g:GroupProfile | (g=m.memberOf && m in p.isMember) => not (g=n.memberOf && n in p.isMember)
}

--fact atLeast_one_admin_per_group


//Pascal: solution of the other group (Andres, Panuya, Fabian): a signature admin_group, with a set of persons.



-- CONTENT ----------------------------------------------
---------------------------------------------------------

sig Content{ //Pascal: why not abstract?
	visible: Visible
}
//Pascal: solution of the other group (Andres, Panuya, Fabian): they have a field created_by, and owned_by in every content, but our solution should be fine too.

fact unique_personalPosts{all disjoint p,q:PersonalProfile, c:Content | c in p.posted => not c in q.posted}
fact unique_groupPosts{all disjoint p,q:GroupProfile, c:Content | c in p.posted => not c in q.posted}
//fact unique_posts{all p:PersonalProfile, q:GroupProfile, c:Content | c in p.posted => not c in q.posted}  

//Pascal: We could sove this more generally with "all disjoint p,q:Profile, c:Content | c in p.posted => not c in q.posted}"

fact post_are_connected{Content in PersonalProfile.posted}

abstract sig CommentableContent extends Content{}
abstract sig PersonalContent extends Content{}

sig Photo extends CommentableContent{}
sig Post extends CommentableContent{
	post: String,
	link: set Photo
//Pascal: can't a post also have a link to other posts?
}
sig Comment extends CommentableContent{
	comment: String,
	refersTo: set CommentableContent
//Pascal: can a comment refer to multiple or no Content? i would rather say it can refer to only one content...
}
//Pascal: what's the visibility of comments? (i will ask the TA)
//Pascal: i think we need an additional fact to make sure that the one who posts a comment actually sees the content to which the comment refers.
//Pascal: we need to make sure that we don't get cyclic comment-chains

sig PersonalMessage extends PersonalContent{
	message: String,
	includedPhoto: lone Photo 	
//Pascal: a personal message can include multiple photos...
//Pascal: don't we need a field for the receiver of the message?
}
sig PersonalDetails extends PersonalContent{
	details:String
}


-- OTHER STUFF -------------------------------------------
---------------------------------------------------------


abstract sig Visible {}
one sig Private, Friends, FriendsOfFriends, TransitiveFriends, Public extends Visible{}




-- OTHER STUFF -------------------------------------------
---------------------------------------------------------

fact canSee{all disjoint p:PersonalProfile,c:Content | 
		(c in p.posted ||
		(c.visible = Friends && c in p.friends.posted) ||
		(c.visible = FriendsOfFriends && (c in p.friends.posted || c in p.friends.friends.posted)) ||
		(c.visible = TransitiveFriends && c in p.^friends.posted) ||
		(c.visible = Public))
		=> c in p.canSee }
//Pascal: We should actually do this as a predicate (Task C)

//Pascal: the receiver of a message can always see it.
//Pascal: we need to make sure that a user can't see contents from users that blocked him
//Pascal: a user can see the private content of his groups


-- TASK C ------------------------------------------------
---------------------------------------------------------

pred canSee [p: personal_profile, c: content] { 
	
}

pred canModify[p:personal_profile, c:content] {

}

pred isOnNewsFeed [p:personal_profile, c:content] {

}

-- TASK D ------------------------------------------------
---------------------------------------------------------

//Invariante 1
//Comment chains are acyclic
assert inv1{
	all c:comment | c not in c.^attached_to
}


//Invariante 2
//A user can modify only content they can see
assert inv2 {
	
}


//Invariante 3
//A user can modify all the content they have created
assert inv3 {

}


//Invariante 4
//If a post or message includes photos, the photos are visible at least to all the people that can view the post
assert inv4 {

} 

//invariante 5
//Each group has members
assert inv5 {
}


//Invariante 6
//A user’s newsfeed only has content visible to her
assert inv6 {

} 


//Invariante 7
//A user cannot see any content created by a user that blocks them
assert inv7 {

}


-- SHOW -------------------------------------------------
---------------------------------------------------------

pred show() {
	all p:PersonalProfile | #p.following >= 1
	all p:PersonalProfile | #p.friends >= 1
	all p:PersonalProfile | #p.posted >= 2
	some p:PersonalProfile | #p.isMember >= 2

//	#Photo >=5
//	#PersonalProfile >= 2
//	#GroupProfile

}

run show for 4 //but 4 Member
	
